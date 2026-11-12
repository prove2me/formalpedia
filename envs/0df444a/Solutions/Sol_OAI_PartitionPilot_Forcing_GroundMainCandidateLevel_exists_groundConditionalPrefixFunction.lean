-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.GroundMainCandidateLevel.exists_groundConditionalPrefixFunction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:16:13.700826+00:00
-- url     : https://prove2.me/submissions/6f3e6f18-f13a-412f-865d-fb265f03fdaa

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

theorem graphRestriction_insert_of_not_mem {A f x y : ZFSet.{u}} (fresh : x ∉ A) :
    graphRestriction A (insert (ZFSet.pair x y) f) = graphRestriction A f := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨a, ha, b, rfl, entry⟩ := mem_graphRestriction.1 hz
    rcases ZFSet.mem_insert_iff.1 entry with eq | entry
    · exact False.elim (fresh ((ZFSet.pair_inj.1 eq).1 ▸ ha))
    · exact pair_mem_graphRestriction.2 ⟨entry, ha⟩
  · intro hz
    obtain ⟨a, ha, b, rfl, entry⟩ := mem_graphRestriction.1 hz
    exact pair_mem_graphRestriction.2 ⟨ZFSet.mem_insert_iff.2 (Or.inr entry), ha⟩

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_CodedInjectiveCones
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

theorem truth_graphDiagonalFormula {n} (f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (graphDiagonalFormula f) env ↔ GraphDiagonalCode (env f) := by
  simp only [graphDiagonalFormula, Truth, truth_imp, truth_orderedPairFormula]
  change (∀ p ∈ env f, ∀ a ∈ p, ∀ x ∈ a, ∀ b ∈ p, ∀ y ∈ b,
    p = ZFSet.pair x y → x = y) ↔ _
  constructor
  · intro h x y entry
    exact h (ZFSet.pair x y) entry {x, y} (ZFSet.mem_pair.2 (Or.inr rfl))
      x (ZFSet.mem_pair.2 (Or.inl rfl)) {x, y} (ZFSet.mem_pair.2 (Or.inr rfl))
      y (ZFSet.mem_pair.2 (Or.inr rfl)) rfl
  · intro h p hp a _ x _ b _ y _ equal
    exact h x y (equal ▸ hp)

theorem truth_graphCompositionFormula {n} (f g h : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (graphCompositionFormula f g h) env ↔ GraphCompositionCode (env f) (env g) (env h) := by
  simp only [graphCompositionFormula, Truth, truth_imp, truth_orderedPairFormula,
    truth_graphFiberEqualityFormula]
  change (∀ p ∈ env f, ∀ a ∈ p, ∀ x ∈ a, ∀ b ∈ p, ∀ y ∈ b,
    p = ZFSet.pair x y → ∀ z, (ZFSet.pair y z ∈ env g ↔ ZFSet.pair x z ∈ env h)) ↔ _
  constructor
  · intro law x y entry
    exact law (ZFSet.pair x y) entry {x, y} (ZFSet.mem_pair.2 (Or.inr rfl))
      x (ZFSet.mem_pair.2 (Or.inl rfl)) {x, y} (ZFSet.mem_pair.2 (Or.inr rfl))
      y (ZFSet.mem_pair.2 (Or.inr rfl)) rfl
  · intro law p hp a _ x _ b _ y _ equal
    exact law x y (equal ▸ hp)

end BoundedFormula

end



section
universe u

theorem graphDiagonalCode_identity (A : ZFSet.{u}) : GraphDiagonalCode (identityFunctionGraph A) :=
  fun x y entry => ((pair_mem_identityFunctionGraph A x y).1 entry).1

theorem graphCompositionCode_relationCompose {A B C f g : ZFSet.{u}}
    (first : ZFSet.IsFunc A B f) (second : ZFSet.IsFunc B C g) :
    GraphCompositionCode f g (relationCompose A B C f g) := by
  intro x y xy z
  constructor
  · intro yz
    have bounds := ZFSet.pair_mem_prod.1 (first.1 xy)
    have target := (ZFSet.pair_mem_prod.1 (second.1 yz)).2
    exact (pair_mem_relationCompose A B C f g x z).2
      ⟨bounds.1, target, y, bounds.2, xy, yz⟩
  · intro xz
    obtain ⟨_, _, v, _, xv, vz⟩ := (pair_mem_relationCompose A B C f g x z).1 xz
    have equal := (show FunctionGraphOn A f from ⟨B, first⟩).unique xv xy
    exact equal ▸ vz





end



end PartitionPilot.Forcing

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

theorem mainStageCode_inj
    {P r μ G m inv one A bottom top height P₂ r₂ μ₂ G₂ m₂ inv₂ one₂ A₂ bottom₂ top₂ height₂ : ZFSet.{u}} :
    mainStageCode P r μ G m inv one A bottom top height = mainStageCode P₂ r₂ μ₂ G₂ m₂ inv₂ one₂ A₂ bottom₂ top₂ height₂ ↔
      P = P₂ ∧ r = r₂ ∧ μ = μ₂ ∧ G = G₂ ∧ m = m₂ ∧ inv = inv₂ ∧ one = one₂ ∧ A = A₂ ∧ bottom = bottom₂ ∧ top = top₂ ∧ height = height₂ := by
  constructor
  · intro equal
    have fields := nonemptyTupleCode_injective 10 equal
    exact ⟨congrFun fields (0 : Fin 11), congrFun fields (1 : Fin 11), congrFun fields (2 : Fin 11), congrFun fields (3 : Fin 11), congrFun fields (4 : Fin 11), congrFun fields (5 : Fin 11), congrFun fields (6 : Fin 11), congrFun fields (7 : Fin 11), congrFun fields (8 : Fin 11), congrFun fields (9 : Fin 11), congrFun fields (10 : Fin 11)⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl

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

theorem realize_functionGraphOnFormula
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    {n} (a f : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (functionGraphOnFormula a f) env ↔ FunctionGraphOn (env a) (env f) := by
  rw [functionGraphOnFormula, realize_ex]
  constructor
  · rintro ⟨B, hB, code⟩
    exact ⟨B, (BoundedFormula.truth_functionFormula a.succ 0 f.succ _).1
      ((BoundedFormula.realize_toFormula M _ _ (Fin.cases hB members)).1 code)⟩
  · intro code
    have range := M.union_mem unions (M.union_mem unions (members f))
    exact ⟨ZFSet.sUnion (ZFSet.sUnion (env f)), range,
      (BoundedFormula.realize_toFormula M _ _ (Fin.cases range members)).2
        ((BoundedFormula.truth_functionFormula a.succ 0 f.succ _).2 code.to_isFunc)⟩

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_FixedTopCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

universe u

theorem fixedTopOrder_bottom {P r b : ZFSet.{u}} (hb : b ∈ P)
    (least : ∀ x ∈ P, ZFSet.pair b x ∈ r) :
    ∀ x ∈ fixedTopCarrier P, ZFSet.pair b x ∈ fixedTopOrder P r := by
  intro x hx
  rcases (mem_fixedTopCarrier P x).1 hx with rfl | oldx
  · exact fixedTopOrder_greatest (fixedTopCarrier_old hb)
  · exact fixedTopOrder_subset P r (least x oldx)

theorem fixedTopOldEmbedding_injection (P : ZFSet.{u}) :
    InjectionCode P (fixedTopCarrier P) (attachmentOldEmbeddingGraph P) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := (mem_attachmentOldEmbeddingGraph P z).1 hz
    exact ZFSet.pair_mem_prod.2 ⟨hx, fixedTopCarrier_old hx⟩
  · intro x hx
    exact ⟨x, (pair_mem_attachmentOldEmbeddingGraph P x x).2 ⟨hx, rfl⟩,
      fun y entry => ((pair_mem_attachmentOldEmbeddingGraph P x y).1 entry).2⟩
  · intro x y z first second
    exact ((pair_mem_attachmentOldEmbeddingGraph P x z).1 first).2.symm.trans
      ((pair_mem_attachmentOldEmbeddingGraph P y z).1 second).2

theorem fixedTopOldEmbedding_code {P r μ : ZFSet.{u}} (old : MeetOrderCode P r μ) :
    MeetEmbeddingCode P (fixedTopCarrier P) r (fixedTopOrder P r) μ (fixedTopMeet P r)
      (attachmentOldEmbeddingGraph P) := by
  refine ⟨fixedTopOldEmbedding_injection P, ?_, ?_⟩
  · intro x y x' y' below first second
    obtain ⟨_, rfl⟩ := (pair_mem_attachmentOldEmbeddingGraph P x x').1 first
    obtain ⟨hy, rfl⟩ := (pair_mem_attachmentOldEmbeddingGraph P y y').1 second
    exact (fixedTopOrder_old_iff hy).2 below
  · intro x y z x' y' z' meet first second third
    obtain ⟨hx, rfl⟩ := (pair_mem_attachmentOldEmbeddingGraph P x x').1 first
    obtain ⟨hy, rfl⟩ := (pair_mem_attachmentOldEmbeddingGraph P y y').1 second
    obtain ⟨_, rfl⟩ := (pair_mem_attachmentOldEmbeddingGraph P z z').1 third
    exact (fixedTopMeet_old_iff old hx hy).2 meet

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_TemplateHeightRangeCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing

universe u

theorem pair_mem_heightImageFamily (I W Qs Bs Hs i R : ZFSet.{u}) :
    ZFSet.pair i R ∈ heightImageFamily I W Qs Bs Hs ↔
      i ∈ I ∧ R ∈ W ∧ heightImageCandidate Qs Bs Hs i R := by
  rw [heightImageFamily, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hi, hR⟩, j, _, S, _, equal, candidate⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hi, hR, candidate⟩
  · rintro ⟨hi, hR, candidate⟩
    exact ⟨⟨hi, hR⟩, i, hi, R, hR, rfl, candidate⟩

namespace BoundedFormula

open SetFormula

theorem truth_heightImageEquationFormula {n} (R Q B h : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (heightImageEquationFormula R Q B h) env ↔
      env R = relationImage (env Q) (env B) (env h) := by
  simp only [heightImageEquationFormula, Truth, truth_imp, truth_imageMemberFormula]
  change ((∀ x ∈ env R, x ∈ env B ∧ ∃ q ∈ env Q, ZFSet.pair q x ∈ env h) ∧
    (∀ x ∈ env B, (∃ q ∈ env Q, ZFSet.pair q x ∈ env h) → x ∈ env R)) ↔ _
  constructor
  · rintro ⟨subset, covers⟩
    apply ZFSet.ext
    intro x
    rw [mem_relationImage]
    exact ⟨subset x, fun hx => covers x hx.1 hx.2⟩
  · intro equal
    constructor
    · intro x hx
      exact (mem_relationImage _ _ _ x).1 (equal ▸ hx)
    · intro x hx image
      exact equal.symm ▸ (mem_relationImage _ _ _ x).2 ⟨hx, image⟩

theorem truth_heightImageCandidateFormula {n} (Qs Bs Hs i R qb bb hb : Fin n)
    (env : Fin n → ZFSet.{u}) (eqQ : env qb = ⋃₀ ⋃₀ env Qs)
    (eqB : env bb = ⋃₀ ⋃₀ env Bs) (eqH : env hb = ⋃₀ ⋃₀ env Hs) :
    Truth (heightImageCandidateFormula Qs Bs Hs i R qb bb hb) env ↔
      heightImageCandidate (env Qs) (env Bs) (env Hs) (env i) (env R) := by
  simp only [heightImageCandidateFormula, truth_exMem, Truth,
    truth_pairMembershipFormula, truth_heightImageEquationFormula]
  change (∃ Q ∈ env qb, ∃ B ∈ env bb, ∃ h ∈ env hb,
    ZFSet.pair (env i) Q ∈ env Qs ∧ ZFSet.pair (env i) B ∈ env Bs ∧
    ZFSet.pair (env i) h ∈ env Hs ∧ env R = relationImage Q B h) ↔ _
  rw [eqQ, eqB, eqH]
  rfl

theorem truth_heightImageFamilyEntryFormula {n} (z I W Qs Bs Hs qb bb hb : Fin n)
    (env : Fin n → ZFSet.{u}) (eqQ : env qb = ⋃₀ ⋃₀ env Qs)
    (eqB : env bb = ⋃₀ ⋃₀ env Bs) (eqH : env hb = ⋃₀ ⋃₀ env Hs) :
    Truth (heightImageFamilyEntryFormula z I W Qs Bs Hs qb bb hb) env ↔
      ∃ i ∈ env I, ∃ R ∈ env W, env z = ZFSet.pair i R ∧
        heightImageCandidate (env Qs) (env Bs) (env Hs) i R := by
  simp only [heightImageFamilyEntryFormula, truth_exMem, Truth, truth_orderedPairFormula]
  apply exists_congr
  intro i
  apply and_congr_right
  intro _
  apply exists_congr
  intro R
  apply and_congr_right
  intro _
  exact and_congr Iff.rfl (truth_heightImageCandidateFormula Qs.succ.succ Bs.succ.succ
    Hs.succ.succ 1 0 qb.succ.succ bb.succ.succ hb.succ.succ
    (extend R (extend i env)) eqQ eqB eqH)

end BoundedFormula

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_CodedProfileImageTests
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

namespace MeetEmbeddingCode
variable {P Q r R μ ν e F x x' : ZFSet.{u}}
variable (embedding : MeetEmbeddingCode P Q r R μ ν e)
variable (source : MeetOrderCode P r μ) (target : MeetOrderCode Q R ν)

include embedding source target in
theorem profilePositive_image_iff (subset : F ⊆ P) (image : ZFSet.pair x x' ∈ e) :
    (∃ f' ∈ relationImage F Q e, ZFSet.pair f' x' ∈ R) ↔
      ∃ f ∈ F, ZFSet.pair f x ∈ r := by
  constructor
  · rintro ⟨f', member, lower⟩
    obtain ⟨_, f, hf, entry⟩ := (mem_relationImage F Q e f').1 member
    exact ⟨f, hf, (embedding.order_iff source target entry image).1 lower⟩
  · rintro ⟨f, hf, lower⟩
    obtain ⟨f', entry, _⟩ := embedding.injection.function.2 f (subset hf)
    exact ⟨f', (mem_relationImage F Q e f').2
      ⟨(ZFSet.pair_mem_prod.1 (embedding.injection.function.1 entry)).2, f, hf, entry⟩,
      embedding.monotone f x f' x' lower entry image⟩

end MeetEmbeddingCode

namespace CodedInsertionProfile
variable {P Q r R μ ν e F c E K c' E' K' x x' : ZFSet.{u}}

theorem at_embedding (profile : CodedInsertionProfile P r μ c E K F)
    (embedding : MeetEmbeddingCode P Q r R μ ν e)
    (source : MeetOrderCode P r μ) (target : MeetOrderCode Q R ν) (subset : F ⊆ P)
    (imageC : ZFSet.pair c c' ∈ e) (imageE : ZFSet.pair E E' ∈ e)
    (imageK : ZFSet.pair K K' ∈ e) (imageX : ZFSet.pair x x' ∈ e)
    (above : ZFSet.pair E' x' ∈ R) :
    ((∃ f' ∈ relationImage F Q e, ZFSet.pair f' x' ∈ R) → ZFSet.pair K' x' ∈ R) ∧
    (¬ (∃ f' ∈ relationImage F Q e, ZFSet.pair f' x' ∈ R) →
      ZFSet.pair (ZFSet.pair K' x') c' ∈ ν) := by
  have hx := (ZFSet.pair_mem_prod.1 (embedding.injection.function.1 imageX)).1
  have old := profile x hx ((embedding.order_iff source target imageE imageX).1 above)
  have positive := embedding.profilePositive_image_iff source target subset imageX
  exact ⟨fun hp => embedding.monotone K x K' x' (old.1 (positive.1 hp)) imageK imageX,
    fun hn => embedding.map_meet K x c K' x' c'
      (old.2 (fun hp => hn (positive.2 hp))) imageK imageX imageC⟩

end CodedInsertionProfile
end PartitionPilot.Forcing

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundTemplateHeightRanges
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

section

namespace PartitionPilot.Forcing

universe u

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem heightImageFamily_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I W Qs Bs Hs : ZFSet.{u}}
    (hI : I ∈ M.sets) (hW : W ∈ M.sets) (hQs : Qs ∈ M.sets)
    (hBs : Bs ∈ M.sets) (hHs : Hs ∈ M.sets) : heightImageFamily I W Qs Bs Hs ∈ M.sets := by
  have qBound := M.union_mem unions (M.union_mem unions hQs)
  have bBound := M.union_mem unions (M.union_mem unions hBs)
  have hBound := M.union_mem unions (M.union_mem unions hHs)
  let params := extend I (extend W (extend Qs (extend Bs (extend Hs
    (extend (⋃₀ ⋃₀ Qs) (extend (⋃₀ ⋃₀ Bs) (extend (⋃₀ ⋃₀ Hs) Fin.elim0)))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.heightImageFamilyEntryFormula 0 1 2 3 4 5 6 7 8) params
    (Fin.cases hI (Fin.cases hW (Fin.cases hQs (Fin.cases hBs (Fin.cases hHs
      (Fin.cases qBound (Fin.cases bBound (Fin.cases hBound (fun i => Fin.elim0 i)))))))))
    (M.prod_mem pairing unions powers separation hI hW)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.heightImageFamilyEntryFormula 0 1 2 3 4 5 6 7 8) (extend z params))
      (ZFSet.prod I W) = heightImageFamily I W Qs Bs Hs := by
    apply ZFSet.ext
    intro z
    rw [heightImageFamily, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl
      (BoundedFormula.truth_heightImageFamilyEntryFormula 0 1 2 3 4 5 6 7 8 _ rfl rfl rfl)
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing

end

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

theorem ordinal_successor_or_nonzeroLimit {T : ZFSet.{u}}
    (ordinal : ordinalSetProperty T) (nonempty : T ≠ ∅) :
    (∃ b ∈ T, T = insert b b) ∨ NonzeroLimitOrdinalCode T := by
  classical
  by_cases further : ∀ b ∈ T, ∃ c ∈ T, b ∈ c
  · exact Or.inr ⟨nonempty, further⟩
  · push Not at further
    obtain ⟨b, member, maximal⟩ := further
    refine Or.inl ⟨b, member, ?_⟩
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_insert_iff]
    constructor
    · intro hx
      have comparison := ordinalMainIndex_total ordinal
        (SetMembers.ofMem x hx) (SetMembers.ofMem b member)
      simp only [ordinalMainIndex_le_iff, SetMembers.raw_ofMem] at comparison
      rcases comparison with before | after
      · exact before
      · rcases after with equal | later
        · exact Or.inl equal.symm
        · exact False.elim (maximal x hx later)
    · rintro (equal | earlier)
      · exact equal.symm ▸ member
      · exact ordinal.1 b member x earlier

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundFunctionRangeFamilies
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing
open SetFormula
universe u v
variable {I : Type v} [Small.{u} I]

theorem TransitiveGround.familyCodeGraph_functionRanges_ground (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (key carriers graphs : I → ZFSet.{u}) (injective : Function.Injective key)
    (domain : ZFSet.range key ∈ M.sets)
    (carriersGround : familyCodeGraph key carriers ∈ M.sets)
    (graphsGround : familyCodeGraph key graphs ∈ M.sets) :
    familyCodeGraph key (fun i => functionGraphRange (carriers i) (graphs i)) ∈ M.sets := by
  let T := ZFSet.range key
  let As := familyCodeGraph key carriers
  let Fs := familyCodeGraph key graphs
  let V := ⋃₀ ⋃₀ Fs
  let B := ⋃₀ ⋃₀ ⋃₀ V
  let Bs := constantFamilyGraph T B
  let W := M.groundPower B
  let result := heightImageFamily T W As Bs Fs
  have hAs := M.union_mem unions (M.union_mem unions carriersGround)
  have hV : V ∈ M.sets := M.union_mem unions (M.union_mem unions graphsGround)
  have hB : B ∈ M.sets := M.union_mem unions (M.union_mem unions (M.union_mem unions hV))
  have hBs : Bs ∈ M.sets := M.constantFamilyGraph_mem pairing unions powers separation domain hB
  have hW : W ∈ M.sets := M.groundPower_mem powers hB
  have ground : result ∈ M.sets :=
    M.heightImageFamily_mem pairing unions powers separation domain hW carriersGround hBs graphsGround
  have aEntry (i : I) : ZFSet.pair (key i) (carriers i) ∈ As :=
    (pair_mem_familyCodeGraph key carriers injective i _).2 rfl
  have fEntry (i : I) : ZFSet.pair (key i) (graphs i) ∈ Fs :=
    (pair_mem_familyCodeGraph key graphs injective i _).2 rfl
  have bEntry (i : I) : ZFSet.pair (key i) B ∈ Bs :=
    (pair_mem_constantFamilyGraph T B _ _).2 ⟨ZFSet.mem_range.2 ⟨i, rfl⟩, rfl⟩
  have valueBound (i : I) {x y : ZFSet.{u}} (entry : ZFSet.pair x y ∈ graphs i) : y ∈ B := by
    have graphBound : graphs i ∈ V := pair_second_mem_doubleUnion (fEntry i)
    exact pair_second_mem_doubleUnion (ZFSet.mem_sUnion.2 ⟨graphs i, graphBound, entry⟩)
  have imageEqual (i : I) :
      functionGraphRange (carriers i) (graphs i) = relationImage (carriers i) B (graphs i) := by
    apply ZFSet.ext
    intro y
    rw [mem_functionGraphRange, mem_relationImage]
    exact ⟨fun h => ⟨valueBound i h.choose_spec.2, h⟩, And.right⟩
  have candidate (i : I) (R : ZFSet.{u}) : heightImageCandidate As Bs Fs (key i) R ↔
      R = functionGraphRange (carriers i) (graphs i) := by
    constructor
    · rintro ⟨A, _, B', _, f, _, ea, eb, ef, equal⟩
      have a := (pair_mem_familyCodeGraph key carriers injective i A).1 ea
      have b := ((pair_mem_constantFamilyGraph T B _ _).1 eb).2
      have f := (pair_mem_familyCodeGraph key graphs injective i f).1 ef
      simpa only [a, b, f, imageEqual i] using equal
    · intro equal
      exact ⟨carriers i, pair_second_mem_doubleUnion (aEntry i),
        B, pair_second_mem_doubleUnion (bEntry i), graphs i, pair_second_mem_doubleUnion (fEntry i),
        aEntry i, bEntry i, fEntry i, equal.trans (imageEqual i)⟩
  have rangeBound (i : I) : functionGraphRange (carriers i) (graphs i) ∈ W := by
    apply (M.mem_groundPower B _).2
    refine ⟨M.functionGraphRange_mem unions separation
      (M.transitive hAs (pair_second_mem_doubleUnion (aEntry i)))
      (M.transitive hV (pair_second_mem_doubleUnion (fEntry i))), ?_⟩
    intro y hy
    obtain ⟨x, _, entry⟩ := (mem_functionGraphRange _ _ y).1 hy
    exact valueBound i entry
  have entries (i : I) (R : ZFSet.{u}) : ZFSet.pair (key i) R ∈ result ↔
      R = functionGraphRange (carriers i) (graphs i) := by
    rw [pair_mem_heightImageFamily, candidate]
    exact ⟨fun h => h.2.2, fun equal =>
      ⟨ZFSet.mem_range.2 ⟨i, rfl⟩, equal.symm ▸ rangeBound i, equal⟩⟩
  have function : FunctionGraphOn T result := by
    refine ⟨W, fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
    intro x hx
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hx
    exact ⟨functionGraphRange (carriers i) (graphs i), (entries i _).2 rfl,
      fun R entry => (entries i R).1 entry⟩
  exact familyCodeGraph_ground_of_entries ground function key _ rfl (fun i => (entries i _).2 rfl)

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundMainCodeRanks
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}

namespace GroundMainStage
variable (stage : GroundMainStage M C D rD) {o : Ordinal.{u}}

theorem field_rank_lt (limit : Order.IsSuccLimit o)
    (points : ZFSet.rank stage.carrier < o) (actors : ZFSet.rank stage.actors < o)
    (columns : ZFSet.rank C < o) (coordinates : ZFSet.rank D < o) :
    ∀ j, ZFSet.rank (stage.field j) < o := by
  have pp := rank_product_lt limit points points
  have gg := rank_product_lt limit actors actors
  have order := (ZFSet.rank_mono stage.meet.order.relation).trans_lt pp
  have meet := rank_functionGraph_lt limit stage.meet.operation pp points
  have mul := rank_functionGraph_lt limit stage.group_code.mul_function gg actors
  have inv := rank_functionGraph_lt limit stage.group_code.inv_function actors actors
  have one := (ZFSet.rank_lt_of_mem stage.group_code.identity_mem).trans actors
  have action := rank_functionGraph_lt limit stage.action_code.function
    (rank_product_lt limit actors points) points
  have bottom := (ZFSet.rank_lt_of_mem stage.bottom_mem).trans points
  have top := (ZFSet.rank_lt_of_mem stage.top_mem).trans points
  have height := rank_functionGraph_lt limit stage.height_code.function points
    (rank_product_lt limit columns coordinates)
  exact Fin.cases points (Fin.cases order (Fin.cases meet (Fin.cases actors (Fin.cases mul
    (Fin.cases inv (Fin.cases one (Fin.cases action (Fin.cases bottom (Fin.cases top
      (Fin.cases height (fun i => Fin.elim0 i)))))))))))

theorem code_rank_lt (limit : Order.IsSuccLimit o)
    (points : ZFSet.rank stage.carrier < o) (actors : ZFSet.rank stage.actors < o)
    (columns : ZFSet.rank C < o) (coordinates : ZFSet.rank D < o) :
    ZFSet.rank stage.code < o :=
  rank_nonemptyTupleCode_lt limit 10 stage.field (stage.field_rank_lt limit points actors columns coordinates)

theorem code_rank_lt_inaccessible
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    (points : ZFSet.rank stage.carrier < ZFSet.rank K) (actors : ZFSet.rank stage.actors < ZFSet.rank K)
    (columns : ZFSet.rank C < ZFSet.rank K) (coordinates : ZFSet.rank D < ZFSet.rank K) :
    ZFSet.rank stage.code < ZFSet.rank K :=
  stage.code_rank_lt (conditions.rank_isLimit pairing unions powers separation infinite hK)
    points actors columns coordinates

end GroundMainStage

namespace GroundMainTransition
variable {source target : GroundMainStage M C D rD}
variable (transition : GroundMainTransition source target) {o : Ordinal.{u}}

theorem graphs_rank_lt (limit : Order.IsSuccLimit o)
    (sourcePoints : ZFSet.rank source.carrier < o) (targetPoints : ZFSet.rank target.carrier < o)
    (sourceActors : ZFSet.rank source.actors < o) (targetActors : ZFSet.rank target.actors < o) :
    ZFSet.rank transition.points < o ∧ ZFSet.rank transition.actors < o :=
  ⟨rank_functionGraph_lt limit transition.point_embedding.injection.function sourcePoints targetPoints,
    rank_functionGraph_lt limit transition.group_embedding.injection.function sourceActors targetActors⟩

theorem code_rank_lt (limit : Order.IsSuccLimit o)
    (sourcePoints : ZFSet.rank source.carrier < o) (targetPoints : ZFSet.rank target.carrier < o)
    (sourceActors : ZFSet.rank source.actors < o) (targetActors : ZFSet.rank target.actors < o) :
    ZFSet.rank transition.code < o := by
  have bounds := transition.graphs_rank_lt limit sourcePoints targetPoints sourceActors targetActors
  exact rank_orderedPair_lt limit bounds.1 bounds.2

end GroundMainTransition
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

theorem value_rank_lt_code (j : Fin 5) {s : ZFSet.{u}} (hs : s ∈ T) :
    ZFSet.rank (fields.value j s) < ZFSet.rank fields.code :=
  (ZFSet.rank_lt_of_mem (pair_second_mem_doubleUnion (fields.value_entry j hs))).trans_le
    (((ZFSet.rank_sUnion_le _).trans (ZFSet.rank_sUnion_le _)).trans (fields.graph_rank_le_code j))

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

theorem fieldValue_rank_lt_code (j : Fin 5) {s : ZFSet.{u}} (hs : s ∈ T) :
    ZFSet.rank (serial.fields.value j s) < ZFSet.rank serial.code :=
  (serial.fields.value_rank_lt_code j hs).trans_le serial.fieldsCode_rank_le_code

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundFixedTopOrders
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

theorem fixedTop_ground_codes
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P r : ZFSet.{u}} (hP : P ∈ M.sets) (hr : r ∈ M.sets) :
    fixedTopCarrier P ∈ M.sets ∧ fixedTopOrder P r ∈ M.sets ∧ fixedTopMeet P r ∈ M.sets ∧
      attachmentOldEmbeddingGraph P ∈ M.sets :=
  ⟨M.fixedTopCarrier_mem pairing unions hP, M.fixedTopOrder_mem pairing unions powers separation hP hr,
    M.fixedTopMeet_mem pairing unions powers separation hP hr,
    M.attachmentOldEmbeddingGraph_mem pairing unions powers separation hP⟩

end PartitionPilot.Forcing.TransitiveGround

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_HeightColumnBoundLaws
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

universe u

theorem mem_heightColumns_of_entry {P C D old x c q : ZFSet.{u}}
    (function : ZFSet.IsFunc P (ZFSet.prod C D) old)
    (entry : ZFSet.pair x (ZFSet.pair c q) ∈ old) : c ∈ heightColumns P C D old := by
  have shape := ZFSet.pair_mem_prod.1 (function.1 entry)
  have coordinates := ZFSet.pair_mem_prod.1 shape.2
  exact (mem_relationImage _ _ _ c).2 ⟨coordinates.1, ZFSet.pair c q,
    (mem_relationImage _ _ _ _).2 ⟨shape.2, x, shape.1, entry⟩,
    (mem_productFirst C D _).2 ⟨c, coordinates.1, q, coordinates.2, rfl⟩⟩

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem heightColumns_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P C D old : ZFSet.{u}} (hP : P ∈ M.sets) (hC : C ∈ M.sets)
    (hD : D ∈ M.sets) (hOld : old ∈ M.sets) : heightColumns P C D old ∈ M.sets :=
  M.relationImage_mem separation
    (M.relationImage_mem separation hP (M.prod_mem pairing unions powers separation hC hD) hOld)
    hC (M.productFirst_mem pairing unions powers separation hC hD)

theorem heightColumns_countable
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {P C D old : ZFSet.{u}} (hP : P ∈ M.sets) (hC : C ∈ M.sets)
    (hD : D ∈ M.sets) (hOld : old ∈ M.sets)
    (small : M.groundEmbeddable (relationImage P (ZFSet.prod C D) old) ZFSet.omega) :
    M.groundEmbeddable (heightColumns P C D old) ZFSet.omega :=
  M.groundEmbeddable_function_image pairing unions powers separation choice
    (M.relationImage_mem separation hP (M.prod_mem pairing unions powers separation hC hD) hOld)
    hC (M.omega_mem separation infinite)
    (M.productFirst_mem pairing unions powers separation hC hD) (productFirst_function C D) small

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



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace GroundChronologyFields
variable {M : TransitiveGround.{u}} {s : ZFSet.{u}}
variable (fields : GroundChronologyFields M (insert s s))
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0) (separation : SeparationSchema M.sets)
variable (newValues : Fin 5 → ZFSet.{u}) (ground : ∀ j, newValues j ∈ M.sets)

theorem replaceTerminal_graph (j : Fin 5) :
    (fields.replaceTerminal pairing unions separation newValues ground).graph j =
      terminalChronologyGraph s (fields.graph j) (newValues j) := rfl

theorem replaceTerminal_value_at (j : Fin 5) :
    (fields.replaceTerminal pairing unions separation newValues ground).value j s = newValues j := by
  apply GroundChronologyFields.value_eq_of_entry
  exact (pair_mem_terminalChronologyGraph _ _ _ _ _).2 (Or.inl ⟨rfl,rfl⟩)

theorem replaceTerminal_value_old (j : Fin 5) {t : ZFSet.{u}} (ht : t ∈ s) :
    (fields.replaceTerminal pairing unions separation newValues ground).value j t = fields.value j t := by
  apply GroundChronologyFields.value_eq_of_entry
  exact (pair_mem_terminalChronologyGraph _ _ _ _ _).2
    (Or.inr ⟨fields.value_entry j (ZFSet.mem_insert_of_mem _ ht),ht⟩)

theorem replaceTerminal_value (j : Fin 5) {t : ZFSet.{u}} (ht : t ∈ insert s s) :
    (fields.replaceTerminal pairing unions separation newValues ground).value j t =
      appendHistoryValue s (fields.value j) (newValues j) t := by
  rcases ZFSet.mem_insert_iff.1 ht with rfl | ht
  · rw [appendHistoryValue_at]
    exact fields.replaceTerminal_value_at pairing unions separation newValues ground j
  · rw [appendHistoryValue_old ht]
    exact fields.replaceTerminal_value_old pairing unions separation newValues ground j ht

theorem replaceTerminal_old_entries (j : Fin 5) {t y : ZFSet.{u}} (ht : t ∈ s) :
    ZFSet.pair t y ∈ (fields.replaceTerminal pairing unions separation newValues ground).graph j ↔
      ZFSet.pair t y ∈ fields.graph j := by
  rw [replaceTerminal_graph, pair_mem_terminalChronologyGraph]
  exact ⟨fun h => h.elim (fun eq => False.elim (ZFSet.mem_irrefl s (eq.1 ▸ ht))) And.left,
    fun entry => Or.inr ⟨entry,ht⟩⟩

end GroundChronologyFields

end PartitionPilot.Forcing



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
universe u

namespace GroundChronologicalMainStage
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (stage : GroundChronologicalMainStage M C D rD)

theorem birth_ground : stage.birth ∈ M.sets :=
  stage.history.birth_mem stage.cutoff (ZFSet.mem_insert _ _)

end GroundChronologicalMainStage

end

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundCompressionHeightSteps
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
universe u

theorem fixedTopHeightGraph_top_iff {P C D old b q y : ZFSet.{u}}
    (function : ZFSet.IsFunc P (ZFSet.prod C D) old) :
    ZFSet.pair P y ∈ fixedTopHeightGraph P old b q ↔ y = ZFSet.pair b q := by
  rw [pair_mem_fixedTopHeightGraph]
  exact ⟨fun h => h.elim And.right (fun h => False.elim
    (ZFSet.mem_irrefl P (ZFSet.pair_mem_prod.1 (function.1 h)).1)),
    fun h => Or.inl ⟨rfl, h⟩⟩

theorem fixedTopHeightGraph_function {P C D old b q : ZFSet.{u}}
    (function : ZFSet.IsFunc P (ZFSet.prod C D) old) (hb : b ∈ C) (hq : q ∈ D) :
    ZFSet.IsFunc (fixedTopCarrier P) (ZFSet.prod C D) (fixedTopHeightGraph P old b q) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    rcases ZFSet.mem_insert_iff.1 hz with rfl | hz
    · exact ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_insert P P, ZFSet.pair_mem_prod.2 ⟨hb, hq⟩⟩
    · obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (function.1 hz)
      exact ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_insert_of_mem P hx, hy⟩
  · intro x hx
    rcases ZFSet.mem_insert_iff.1 hx with rfl | hx
    · refine ⟨ZFSet.pair b q, ZFSet.mem_insert _ _, ?_⟩
      intro y hy
      exact (fixedTopHeightGraph_top_iff function).1 hy
    · obtain ⟨y, entry, unique⟩ := function.2 x hx
      refine ⟨y, (fixedTopHeightGraph_old_iff hx).2 entry, ?_⟩
      intro z hz
      exact unique z ((fixedTopHeightGraph_old_iff hx).1 hz)

theorem fixedTopHeightGraph_strict {P C D r old rD b q : ZFSet.{u}}
    (code : StrictLexHeightCode P C D r old rD) (order : PartialOrderCode P r)
    (hb : b ∈ C) (hq : q ∈ D)
    (above : ∀ c ∈ heightColumns P C D old, c ∈ b) :
    StrictLexHeightCode (fixedTopCarrier P) C D (fixedTopOrder P r)
      (fixedTopHeightGraph P old b q) rD := by
  refine ⟨fixedTopHeightGraph_function code.function hb hq, ?_⟩
  intro x hx y hy c v d w lower different xEntry yEntry
  rcases ZFSet.mem_union.1 lower with lower | top
  · have bounds := ZFSet.pair_mem_prod.1 (order.relation lower)
    exact code.strict x bounds.1 y bounds.2 c v d w lower different
      ((fixedTopHeightGraph_old_iff bounds.1).1 xEntry)
      ((fixedTopHeightGraph_old_iff bounds.2).1 yEntry)
  · obtain ⟨_, yP⟩ := ZFSet.pair_mem_prod.1 top
    have yEq : y = P := ZFSet.mem_singleton.1 yP
    subst y
    have hxOld : x ∈ P := (ZFSet.mem_insert_iff.1 hx).resolve_left different
    have oldEntry := (fixedTopHeightGraph_old_iff hxOld).1 xEntry
    have eq := ZFSet.pair_inj.1 ((fixedTopHeightGraph_top_iff code.function).1 yEntry)
    rcases eq with ⟨rfl, rfl⟩
    exact Or.inl (above c (mem_heightColumns_of_entry code.function oldEntry))

theorem fixedTopHeightGraph_range {P C D old b q : ZFSet.{u}}
    (function : ZFSet.IsFunc P (ZFSet.prod C D) old) (hb : b ∈ C) (hq : q ∈ D) :
    relationImage (fixedTopCarrier P) (ZFSet.prod C D) (fixedTopHeightGraph P old b q) =
      insert (ZFSet.pair b q) (relationImage P (ZFSet.prod C D) old) := by
  apply ZFSet.ext
  intro y
  rw [mem_relationImage, ZFSet.mem_insert_iff, mem_relationImage]
  constructor
  · rintro ⟨hy, x, hx, entry⟩
    rcases (pair_mem_fixedTopHeightGraph P old b q x y).1 entry with ⟨_, eq⟩ | oldEntry
    · exact Or.inl eq
    · exact Or.inr ⟨hy, x, (ZFSet.pair_mem_prod.1 (function.1 oldEntry)).1, oldEntry⟩
  · rintro (rfl | ⟨hy, x, hx, entry⟩)
    · exact ⟨ZFSet.pair_mem_prod.2 ⟨hb, hq⟩, P, ZFSet.mem_insert P P,
        (pair_mem_fixedTopHeightGraph P old b q P _).2 (Or.inl ⟨rfl, rfl⟩)⟩
    · exact ⟨hy, x, ZFSet.mem_insert_of_mem P hx,
        (pair_mem_fixedTopHeightGraph P old b q x y).2 (Or.inr entry)⟩

theorem fixedTopHeightGraph_old_lt_top {P C D old rD b q x y : ZFSet.{u}}
    (function : ZFSet.IsFunc P (ZFSet.prod C D) old) (hb : b ∈ C) (hq : q ∈ D)
    (above : ∀ c ∈ heightColumns P C D old, c ∈ b) (entry : ZFSet.pair x y ∈ old) :
    ZFSet.pair y (ZFSet.pair b q) ∈ lexHeightOrder C D rD := by
  have yShape := (ZFSet.pair_mem_prod.1 (function.1 entry)).2
  obtain ⟨c, hc, v, hv, rfl⟩ := ZFSet.mem_prod.1 yShape
  exact (pair_mem_lexHeightOrder C D rD c v b q).2
    ⟨hc, hv, hb, hq, Or.inl (above c (mem_heightColumns_of_entry function entry))⟩

theorem fixedTopHeightGraph_bound {P C D old rD b q x y : ZFSet.{u}}
    (function : ZFSet.IsFunc P (ZFSet.prod C D) old) (hb : b ∈ C) (hq : q ∈ D)
    (above : ∀ c ∈ heightColumns P C D old, c ∈ b)
    (entry : ZFSet.pair x y ∈ fixedTopHeightGraph P old b q) :
    y = ZFSet.pair b q ∨ ZFSet.pair y (ZFSet.pair b q) ∈ lexHeightOrder C D rD := by
  rcases (pair_mem_fixedTopHeightGraph P old b q x y).1 entry with newEntry | oldEntry
  · exact Or.inl newEntry.2
  · exact Or.inr (fixedTopHeightGraph_old_lt_top function hb hq above oldEntry)






end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)

include pairing unions in
theorem fixedTopHeightGraph_mem {P old b q : ZFSet.{u}}
    (hP : P ∈ M.sets) (hOld : old ∈ M.sets) (hb : b ∈ M.sets) (hq : q ∈ M.sets) :
    fixedTopHeightGraph P old b q ∈ M.sets :=
  M.insert_mem pairing unions
    (M.orderedPair_mem pairing hP (M.orderedPair_mem pairing hb hq)) hOld

include choice in
theorem exists_fixedTopHeight
    {P D r old rD : ZFSet.{u}} (hP : P ∈ M.sets) (hD : D ∈ M.sets)
    (hOld : old ∈ M.sets) (order : PartialOrderCode P r) (nonempty : D.Nonempty)
    (code : StrictLexHeightCode P
      (M.groundOmegaOne pairing unions powers separation collection infinite) D r old rD)
    (small : M.groundEmbeddable (relationImage P (ZFSet.prod
      (M.groundOmegaOne pairing unions powers separation collection infinite) D) old) ZFSet.omega) :
    let C := M.groundOmegaOne pairing unions powers separation collection infinite
    ∃ b ∈ C, ∃ q ∈ D, ∃ height ∈ M.sets,
      height = fixedTopHeightGraph P old b q ∧
      (∀ c ∈ heightColumns P C D old, c ∈ b) ∧
      b ∉ heightColumns P C D old ∧
      StrictLexHeightCode (fixedTopCarrier P) C D (fixedTopOrder P r) height rD ∧
      (∀ x ∈ P, ∀ y, ZFSet.pair x y ∈ height ↔ ZFSet.pair x y ∈ old) ∧
      (∀ y, ZFSet.pair P y ∈ height ↔ y = ZFSet.pair b q) ∧
      relationImage (fixedTopCarrier P) (ZFSet.prod C D) height =
        insert (ZFSet.pair b q) (relationImage P (ZFSet.prod C D) old) ∧
      relationImage (fixedTopCarrier P) (ZFSet.prod C D) height ∈ M.sets ∧
      M.groundEmbeddable (relationImage (fixedTopCarrier P) (ZFSet.prod C D) height) ZFSet.omega ∧
      (∀ x y, ZFSet.pair x y ∈ old →
        ZFSet.pair y (ZFSet.pair b q) ∈ lexHeightOrder C D rD) ∧
      (∀ x y, ZFSet.pair x y ∈ height →
        y = ZFSet.pair b q ∨ ZFSet.pair y (ZFSet.pair b q) ∈ lexHeightOrder C D rD) := by
  let C := M.groundOmegaOne pairing unions powers separation collection infinite
  change ∃ b ∈ C, ∃ q ∈ D, ∃ height ∈ M.sets, _
  have hC : C ∈ M.sets :=
    (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
  have hK := M.heightColumns_mem pairing unions powers separation hP hC hD hOld
  have smallK := M.heightColumns_countable pairing unions powers separation infinite choice
    hP hC hD hOld small
  have subset : heightColumns P C D old ⊆ C :=
    fun x hx => ((mem_relationImage _ C _ x).1 hx).1
  obtain ⟨b, hb, above⟩ := M.groundOmegaOne_countable_bound pairing unions powers separation
    collection infinite choice hK subset smallK
  obtain ⟨q, hq⟩ := nonempty
  have hbM := M.transitive hC hb
  have hqM := M.transitive hD hq
  have hPair := M.orderedPair_mem pairing hbM hqM
  have hRange := M.relationImage_mem separation hP
    (M.prod_mem pairing unions powers separation hC hD) hOld
  have rangeEq := fixedTopHeightGraph_range code.function hb hq
  refine ⟨b, hb, q, hq, fixedTopHeightGraph P old b q,
    M.fixedTopHeightGraph_mem pairing unions hP hOld hbM hqM, rfl, above,
    fun h => ZFSet.mem_irrefl b (above b h),
    fixedTopHeightGraph_strict code order hb hq above,
    fun x hx y => fixedTopHeightGraph_old_iff hx,
    fun y => fixedTopHeightGraph_top_iff code.function, rangeEq, ?_, ?_, ?_, ?_⟩
  · rw [rangeEq]
    exact M.insert_mem pairing unions hPair hRange
  · rw [rangeEq]
    exact M.groundEmbeddable_insert pairing unions powers separation infinite hRange hPair small
  · intro x y entry
    exact fixedTopHeightGraph_old_lt_top code.function hb hq above entry
  · intro x y entry
    exact fixedTopHeightGraph_bound code.function hb hq above entry

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundFixedTopStep
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

theorem exists_fixedTopExtension
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {P r μ G m e A D rD old : ZFSet.{u}}
    (hP : P ∈ M.sets) (hr : r ∈ M.sets) (hG : G ∈ M.sets) (hA : A ∈ M.sets)
    (hD : D ∈ M.sets) (hOld : old ∈ M.sets)
    (meet : MeetOrderCode P r μ) (action : PosetActionCode G P m e r A)
    (one_mem : e ∈ G) (nonempty : D.Nonempty)
    (height : StrictLexHeightCode P
      (M.groundOmegaOne pairing unions powers separation collection infinite) D r old rD)
    (small : M.groundEmbeddable (relationImage P (ZFSet.prod
      (M.groundOmegaOne pairing unions powers separation collection infinite) D) old) ZFSet.omega) :
    let C := M.groundOmegaOne pairing unions powers separation collection infinite
    ∃ b ∈ C, ∃ q ∈ D,
      fixedTopCarrier P ∈ M.sets ∧ fixedTopOrder P r ∈ M.sets ∧ fixedTopMeet P r ∈ M.sets ∧
      attachmentOldEmbeddingGraph P ∈ M.sets ∧ fixedTopAction G P A ∈ M.sets ∧
      fixedTopHeightGraph P old b q ∈ M.sets ∧
      MeetOrderCode (fixedTopCarrier P) (fixedTopOrder P r) (fixedTopMeet P r) ∧
      MeetEmbeddingCode P (fixedTopCarrier P) r (fixedTopOrder P r) μ (fixedTopMeet P r)
        (attachmentOldEmbeddingGraph P) ∧
      PosetActionCode G (fixedTopCarrier P) m e (fixedTopOrder P r) (fixedTopAction G P A) ∧
      StrictLexHeightCode (fixedTopCarrier P) C D (fixedTopOrder P r)
        (fixedTopHeightGraph P old b q) rD ∧
      (∀ x ∈ fixedTopCarrier P, ZFSet.pair x P ∈ fixedTopOrder P r) ∧
      (∀ x ∈ P, ZFSet.pair P x ∉ fixedTopOrder P r) ∧
      (∀ x y, y ∈ P → (ZFSet.pair x y ∈ fixedTopOrder P r ↔ ZFSet.pair x y ∈ r)) ∧
      (∀ x y, y ∈ P → ZFSet.pair x y ∈ fixedTopOrder P r → x ∈ P) ∧
      (∀ g ∈ G, ZFSet.pair (ZFSet.pair g P) P ∈ fixedTopAction G P A) ∧
      (∀ g x y, x ∈ P → (ZFSet.pair (ZFSet.pair g x) y ∈ fixedTopAction G P A ↔
        ZFSet.pair (ZFSet.pair g x) y ∈ A)) ∧
      (∀ x ∈ P, ∀ y, ZFSet.pair x y ∈ fixedTopHeightGraph P old b q ↔ ZFSet.pair x y ∈ old) ∧
      (∀ c ∈ heightColumns P C D old, c ∈ b) ∧ b ∉ heightColumns P C D old ∧
      relationImage (fixedTopCarrier P) (ZFSet.prod C D) (fixedTopHeightGraph P old b q) =
        insert (ZFSet.pair b q) (relationImage P (ZFSet.prod C D) old) ∧
      relationImage (fixedTopCarrier P) (ZFSet.prod C D) (fixedTopHeightGraph P old b q) ∈ M.sets ∧
      M.groundEmbeddable
        (relationImage (fixedTopCarrier P) (ZFSet.prod C D) (fixedTopHeightGraph P old b q)) ZFSet.omega ∧
      (∀ x y, ZFSet.pair x y ∈ old →
        ZFSet.pair y (ZFSet.pair b q) ∈ lexHeightOrder C D rD) ∧
      (∀ x y, ZFSet.pair x y ∈ fixedTopHeightGraph P old b q →
        y = ZFSet.pair b q ∨ ZFSet.pair y (ZFSet.pair b q) ∈ lexHeightOrder C D rD) := by
  obtain ⟨b, hb, q, hq, newHeight, hNewHeight, equal, above, fresh, strict,
    oldEntries, _, rangeEq, hRange, smallRange, oldBound, bound⟩ :=
    M.exists_fixedTopHeight pairing unions powers separation collection infinite choice
      hP hD hOld meet.order nonempty height small
  subst newHeight
  obtain ⟨hL, hR, hMeet, hEmbedding⟩ := M.fixedTop_ground_codes pairing unions powers separation hP hr
  exact ⟨b, hb, q, hq, hL, hR, hMeet, hEmbedding,
    M.fixedTopAction_mem pairing unions powers separation hG hP hA, hNewHeight,
    fixedTopMeet_code meet, fixedTopOldEmbedding_code meet, action.fixedTop meet.order one_mem,
    strict, fun _ hx => fixedTopOrder_greatest hx,
    fun _ hx => (fixedTopOrder_strict_top meet.order hx).2,
    fun _ _ hy => fixedTopOrder_old_iff hy,
    fun _ _ hy entry => fixedTopOrder_no_new_below meet.order hy entry,
    fun _ hg => fixedTopAction_fixes_top hg, fun _ _ _ hx => fixedTopAction_old_iff hx,
    oldEntries, above, fresh, rangeEq, hRange, smallRange, oldBound, bound⟩

end TransitiveGround

open SetRealization
universe u

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainStageInvariant
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

open SetFormula SetRealization
universe u

namespace GroundChronologicalMainStage
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}

namespace Invariant
variable {source : GroundChronologicalMainStage M C D rD} {K Labels : ZFSet.{u}}
variable (invariant : source.Invariant K Labels)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
include invariant pairing unions powers separation infinite hK conditions

theorem code_rank_lt : ZFSet.rank source.stage.code < ZFSet.rank K :=
  source.stage.code_rank_lt_inaccessible pairing unions powers separation infinite hK conditions
    invariant.points_rank invariant.actors_rank invariant.columns_rank invariant.coordinates_rank

end Invariant

end GroundChronologicalMainStage

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
universe u

namespace GroundChronologicalMainTransition
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable {source target : GroundChronologicalMainStage M C D rD}
variable (sourceFields : GroundChronologyFields M (insert source.cutoff source.cutoff))
variable (targetFields : GroundChronologyFields M (insert target.cutoff target.cutoff))
variable (sourceAgreement : ∀ j s, s ∈ insert source.cutoff source.cutoff →
  sourceFields.value j s = source.history.fieldValue j s)
variable (targetAgreement : ∀ j s, s ∈ insert target.cutoff target.cutoff →
  targetFields.value j s = target.history.fieldValue j s)

include sourceAgreement targetAgreement

theorem field_laws (transition : GroundChronologicalMainTransition source target) :
    ChronologicalTransitionLaws transition.map.points source.cutoff target.cutoff source.birth target.birth
      sourceFields.graph targetFields.graph := by
  refine ⟨transition.cutoff_le, transition.birth, ?_⟩
  apply (sourceFields.graphPrefixCode_iff_values targetFields (fun s before =>
    ⟨ZFSet.mem_insert_iff.2 before, ZFSet.mem_insert_iff.2 (transition.prefix_bound before)⟩)).2
  intro j s before
  rw [sourceAgreement j s (ZFSet.mem_insert_iff.2 before),
    targetAgreement j s (ZFSet.mem_insert_iff.2 (transition.prefix_bound before))]
  have h := transition.history_prefix s before
  exact Fin.cases h.1.symm (Fin.cases h.2.1.symm (Fin.cases h.2.2.1.symm
    (Fin.cases h.2.2.2.1.symm (Fin.cases h.2.2.2.2.symm (fun i => Fin.elim0 i))))) j

end GroundChronologicalMainTransition
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace GroundLinkedMainStage
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable (linked : GroundLinkedMainStage M K Labels C D rD)

theorem code_rank_lt
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) (hK : K ∈ M.sets)
    (conditions : GroundInaccessibleConditions M K) : ZFSet.rank linked.code < ZFSet.rank K :=
  rank_nonemptyTupleCode_lt (conditions.rank_isLimit pairing unions powers separation infinite hK) 2 _
    (Fin.cases (linked.invariant.code_rank_lt pairing unions powers separation infinite hK conditions)
      (Fin.cases (ZFSet.rank_lt_of_mem linked.invariant.cutoff_mem) (fun _ => linked.serial_rank)))

end GroundLinkedMainStage

end PartitionPilot.Forcing



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

theorem code_ground : run.code ∈ M.sets :=
  M.nonemptyTupleCode_mem pairing 2 _ (Fin.cases run.indices_ground
    (Fin.cases run.stages_ground (fun _ => run.transitions_ground)))

theorem stageGraph_function : FunctionGraphOn run.indices run.stageGraph :=
  familyCodeGraph_function run.key _ run.key_injective

theorem transitionGraph_function : FunctionGraphOn (chronologyPairs run.indices) run.transitionGraph := by
  have function := familyCodeGraph_function (mainTransitionIndexKey run.key)
    (fun p => (run.diagram.transition p.property).map.code)
    (mainTransitionIndexKey_injective run.key run.key_injective)
  rw [mainTransitionIndex_range run.key run.key_order] at function
  exact function

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

namespace LinkedMainStageRawCode
variable {M : TransitiveGround.{u}} {K Labels C D rD N z : ZFSet.{u}}
variable {f g : Fin 24 → ZFSet.{u}}

theorem exists_linked_fields
    (raw : LinkedMainStageRawCode M K Labels C D rD N z f)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (ground : ∀ j, f j ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (omega : N = ZFSet.omega) :
    ∃ linked : GroundLinkedMainStage M K Labels C D rD, linked.code = z ∧ linked.rawFields = f := by
  obtain ⟨linked, equal⟩ := raw.exists_linked pairing unions powers separation ground hC hD hrD omega
  refine ⟨linked, equal, ?_⟩
  rw [omega] at raw
  have actual := linked.rawFields_code
  rw [equal] at actual
  exact actual.fields_unique raw

end LinkedMainStageRawCode
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

theorem retargetEq_code
    (transition : GroundChronologicalMainTransition source target)
    (sourceEqual : source = first) (targetEqual : target = second) :
    (transition.retargetEq sourceEqual targetEqual).map.code = transition.map.code := by
  cases sourceEqual
  cases targetEqual
  rfl

theorem retargetEq_coversOldBirths_iff
    (transition : GroundChronologicalMainTransition source target)
    (sourceEqual : source = first) (targetEqual : target = second) :
    (transition.retargetEq sourceEqual targetEqual).CoversOldBirths ↔ transition.CoversOldBirths := by
  cases sourceEqual
  cases targetEqual
  rfl

end PartitionPilot.Forcing.GroundChronologicalMainTransition

end

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

theorem realize_oldProfilePreservationFormula (M : TransitiveGround.{u}) {n}
    (P r μ Q R ν e Filters : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (oldProfilePreservationFormula P r μ Q R ν e Filters).toFormula env ↔
      OldProfilePreservationCode (env P) (env r) (env μ) (env Q) (env R) (env ν)
        (env e) (env Filters) :=
  (realize_toFormula M _ env members).trans
    (truth_oldProfilePreservationFormula P r μ Q R ν e Filters env)

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_OldProfilePreservationComposition
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

theorem relationImage_identity_on {P F : ZFSet.{u}} (subset : F ⊆ P) :
    relationImage F P (identityFunctionGraph P) = F := by
  apply ZFSet.ext
  intro y
  rw [mem_relationImage]
  constructor
  · rintro ⟨_, x, hx, entry⟩
    exact ((pair_mem_identityFunctionGraph P x y).1 entry).1 ▸ hx
  · intro hy
    exact ⟨subset hy, y, hy, (pair_mem_identityFunctionGraph P y y).2 ⟨rfl, subset hy⟩⟩

theorem relationImage_composition_on {P Q V F e f : ZFSet.{u}} (subset : F ⊆ P) :
    relationImage (relationImage F Q e) V f = relationImage F V (relationCompose P Q V e f) := by
  apply ZFSet.ext
  intro z
  rw [mem_relationImage, mem_relationImage]
  constructor
  · rintro ⟨hz, y, hy, yz⟩
    obtain ⟨hy, x, hx, xy⟩ := (mem_relationImage F Q e y).1 hy
    exact ⟨hz, x, hx, (pair_mem_relationCompose P Q V e f x z).2
      ⟨subset hx, hz, y, hy, xy, yz⟩⟩
  · rintro ⟨hz, x, hx, entry⟩
    obtain ⟨_, _, y, hy, xy, yz⟩ := (pair_mem_relationCompose P Q V e f x z).1 entry
    exact ⟨hz, y, (mem_relationImage F Q e y).2 ⟨hy, x, hx, xy⟩, yz⟩

namespace OldProfilePreservationCode

theorem identity (P r μ Filters : ZFSet.{u}) :
    OldProfilePreservationCode P r μ P r μ (identityFunctionGraph P) Filters := by
  intro F _ c _ E _ K _ profile c' _ E' _ K' _ first second third
  obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph P c c').1 first
  obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph P E E').1 second
  obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph P K K').1 third
  rw [relationImage_identity_on profile.filter_subset]
  exact profile

theorem comp_ground (M : TransitiveGround.{u}) (separation : SeparationSchema M.sets)
    {P r μ Q R ν V S ξ e f : ZFSet.{u}}
    (first : OldProfilePreservationCode P r μ Q R ν e (M.groundPower P))
    (second : OldProfilePreservationCode Q R ν V S ξ f (M.groundPower Q))
    (hQ : Q ∈ M.sets) (he : e ∈ M.sets) :
    OldProfilePreservationCode P r μ V S ξ (relationCompose P Q V e f) (M.groundPower P) := by
  intro F hF c hc E hE K hK profile c' hc' E' hE' K' hK' imageC imageE imageK
  obtain ⟨_, _, a, ha, ca, ac⟩ := (pair_mem_relationCompose P Q V e f c c').1 imageC
  obtain ⟨_, _, b, hb, Eb, bE⟩ := (pair_mem_relationCompose P Q V e f E E').1 imageE
  obtain ⟨_, _, d, hd, Kd, dK⟩ := (pair_mem_relationCompose P Q V e f K K').1 imageK
  have intermediate := first F hF c hc E hE K hK profile a ha b hb d hd ca Eb Kd
  have imageGround := M.relationImage_mem separation ((M.mem_groundPower P F).1 hF).1 hQ he
  have imageMember := (M.mem_groundPower Q (relationImage F Q e)).2
    ⟨imageGround, fun _ hx => ((mem_relationImage _ _ _ _).1 hx).1⟩
  have result := second _ imageMember a ha b hb d hd intermediate
    c' hc' E' hE' K' hK' ac bE dK
  rw [relationImage_composition_on profile.filter_subset] at result
  exact result

end OldProfilePreservationCode

end PartitionPilot.Forcing

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundBatchEarlierLayerWitnesses
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

theorem CountableLayerCode.of_literal_extension
    {A B old born t D N injection : ZFSet.{u}}
    (code : CountableLayerCode A old t D N injection)
    (fiber : ∀ x ∈ B, ZFSet.pair x t ∈ born → x ∈ A ∧ ZFSet.pair x t ∈ old) :
    CountableLayerCode B born t D N injection :=
  ⟨code.small, fun x hx entry => code.cover x (fiber x hx entry).1 (fiber x hx entry).2⟩

theorem CopyLayerCode.of_literal_extension
    {Qs rs μs A B rA rB μA μB old born t I parts Indices Maps W N injection : ZFSet.{u}}
    (code : CopyLayerCode Qs rs μs A rA μA old t I parts Indices Maps W N injection)
    (carrier : A ⊆ B) (order : rA ⊆ rB) (meets : μA ⊆ μB)
    (fiber : ∀ x ∈ B, ZFSet.pair x t ∈ born → x ∈ A ∧ ZFSet.pair x t ∈ old) :
    CopyLayerCode Qs rs μs B rB μB born t I
      (ZFSet.sep (fun p => p ∈ ZFSet.prod I A) parts) Indices Maps W N injection := by
  refine ⟨code.small, code.indices, code.maps, ?_, ?_, ?_⟩
  · intro i hi s hs e P R V index map qField rField mField
    exact (code.embedding i hi s hs e P R V index map qField rField mField).enlarge_target
      carrier order meets
  · intro x hx entry
    have retained := fiber x hx entry
    obtain ⟨i, hi, part⟩ := code.cover x retained.1 retained.2
    exact ⟨i, hi, ZFSet.mem_sep.2 ⟨part, ZFSet.pair_mem_prod.2 ⟨hi, retained.1⟩⟩⟩
  · intro i hi s hs e P x _ index map qField part
    have retained := ZFSet.mem_sep.1 part
    exact relationImage_enlarge_target carrier
      (code.inCopy i hi s hs e P x (ZFSet.pair_mem_prod.1 retained.2).2 index map qField retained.1)

theorem SeparatedLayerCode.of_literal_extension
    {Qs rs μs A B rA rB μA μB old born t I Indices Maps W Components F : ZFSet.{u}}
    (code : SeparatedLayerCode Qs rs μs A rA μA old t I Indices Maps W Components F)
    (carrier : A ⊆ B) (order : rA ⊆ rB) (meets : μA ⊆ μB) (births : old ⊆ born)
    (fiber : ∀ x ∈ B, ZFSet.pair x t ∈ born → x ∈ A ∧ ZFSet.pair x t ∈ old) :
    SeparatedLayerCode Qs rs μs B rB μB born t I Indices Maps W Components F := by
  refine ⟨code.indices, code.maps, ?_, code.components, ?_, ?_, ?_⟩
  · rw [code.fiber]
    apply ZFSet.ext
    intro x
    rw [mem_layerBirthFiber, mem_layerBirthFiber]
    exact ⟨fun h => ⟨carrier h.1, births h.2⟩, fun h => fiber x h.1 h.2⟩
  · intro i hi s hs e P R V index map qField rField mField
    exact (code.embedding i hi s hs e P R V index map qField rField mField).enlarge_target
      carrier order meets
  · intro i hi s hs e P x _ index map qField component
    have inF := (ZFSet.pair_mem_prod.1 (code.components.1 component)).1
    have hx : x ∈ A := ((mem_layerBirthFiber A old t x).1 (code.fiber ▸ inF)).1
    exact relationImage_enlarge_target carrier (code.cover i hi s hs e P x hx index map qField component)
  · intro x hx y hy i hi j hj first second different
    exact (code.separated x hx y hy i hi j hj first second different).of_literal_extension
      carrier order meets births

theorem fixedTopLayerWitness_code {Qs rs μs P r birth s : ZFSet.{u}}
    (earlier : ∀ x t, ZFSet.pair x t ∈ birth → t ∈ s) :
    GrowthLayerWitnessCode Qs rs μs (fixedTopCarrier P) (fixedTopOrder P r)
      (fixedTopMeet P r) (fixedTopBirth P birth s) s ZFSet.omega (fixedTopLayerWitness P) := by
  refine Or.inl ⟨{P}, {ZFSet.pair P ∅}, rfl, fixedTopBirth_singleton_injection P, ?_⟩
  intro x _ entry
  exact ZFSet.mem_singleton.2 ((fixedTopBirth_new_time_iff earlier).1 entry)

theorem TransitiveGround.fixedTopLayerWitness_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {P : ZFSet.{u}} (hP : P ∈ M.sets) : fixedTopLayerWitness P ∈ M.sets := by
  have singleton (x : ZFSet.{u}) (hx : x ∈ M.sets) : ({x} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hx hx
  exact M.countableLayerWitness_mem pairing (singleton P hP)
    (singleton _ (M.orderedPair_mem pairing hP (M.empty_mem ⟨P, hP⟩)))

end

namespace GrowthLayerWitnessCode
open SetFormula
universe u

theorem exists_literal_extension_rank_lt {M : TransitiveGround.{u}}
    {Qs rs μs A B rA rB μA μB old born t N z : ZFSet.{u}}
    (code : GrowthLayerWitnessCode Qs rs μs A rA μA old t N z)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0) (separation : SeparationSchema M.sets)
    (hA : A ∈ M.sets) (hz : z ∈ M.sets)
    {o : Ordinal.{u}} (limit : Order.IsSuccLimit o) (rank : ZFSet.rank z < o)
    (carrier : A ⊆ B) (order : rA ⊆ rB) (meets : μA ⊆ μB) (births : old ⊆ born)
    (fiber : ∀ x ∈ B, ZFSet.pair x t ∈ born → x ∈ A ∧ ZFSet.pair x t ∈ old) :
    ∃ z' ∈ M.sets, GrowthLayerWitnessCode Qs rs μs B rB μB born t N z' ∧
      ZFSet.rank z' < o := by
  rcases code with ⟨D, injection, rfl, code⟩ |
    ⟨I, parts, Indices, Maps, W, injection, rfl, code⟩ |
    ⟨I, Indices, Maps, W, Components, F, rfl, code⟩
  · exact ⟨countableLayerWitness D injection, hz,
      Or.inl ⟨D, injection, rfl, code.of_literal_extension fiber⟩, rank⟩
  · have fields := M.nonemptyTupleCode_field_mem 6 _ hz
    have ranks := fun j => (rank_nonemptyTupleCode_field_le 6 _ j).trans_lt rank
    let retained := ZFSet.sep (fun p => p ∈ ZFSet.prod I A) parts
    have ground : retained ∈ M.sets :=
      M.injection_restriction_mem separation (fields 1) hA (fields 2)
    have retainedRank : ZFSet.rank retained < o :=
      (ZFSet.rank_mono (show retained ⊆ parts from fun _ hp => (ZFSet.mem_sep.1 hp).1)).trans_lt (ranks 2)
    exact ⟨copyLayerWitness I retained Indices Maps W injection,
      M.copyLayerWitness_mem pairing unions (fields 1) ground (fields 3) (fields 4) (fields 5) (fields 6),
      Or.inr (Or.inl ⟨I, retained, Indices, Maps, W, injection, rfl,
        code.of_literal_extension carrier order meets fiber⟩),
      copyLayerWitness_rank_lt limit (ranks 1) retainedRank (ranks 3) (ranks 4) (ranks 5) (ranks 6)⟩
  · exact ⟨separatedLayerWitness I Indices Maps W Components F, hz,
      Or.inr (Or.inr ⟨I, Indices, Maps, W, Components, F, rfl,
        code.of_literal_extension carrier order meets births fiber⟩), rank⟩

end GrowthLayerWitnessCode

section
open SetFormula SetRealization
universe u

theorem GrowthLayerWitnessCode.exists_fixedTop_earlier_rank_lt
    {M : TransitiveGround.{u}} {Qs rs μs P r μ T birth s t N z : ZFSet.{u}}
    (code : GrowthLayerWitnessCode Qs rs μs P r μ birth t N z)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0) (separation : SeparationSchema M.sets)
    (hP : P ∈ M.sets) (hz : z ∈ M.sets)
    {o : Ordinal.{u}} (limit : Order.IsSuccLimit o) (rank : ZFSet.rank z < o)
    (meet : MeetOrderCode P r μ) (born : ZFSet.IsFunc P T birth) (before : t ∈ s) :
    ∃ z' ∈ M.sets, GrowthLayerWitnessCode Qs rs μs (fixedTopCarrier P)
      (fixedTopOrder P r) (fixedTopMeet P r) (fixedTopBirth P birth s) t N z' ∧
      ZFSet.rank z' < o := by
  apply code.exists_literal_extension_rank_lt pairing unions separation hP hz limit rank
    (fixedTopCarrier_subset P) (fixedTopOrder_subset P r) (fixedTopMeet_subset meet)
    (fixedTopBirth_subset P birth s)
  intro x _ entry
  have old := (fixedTopBirth_earlier_iff before).1 entry
  exact ⟨(ZFSet.pair_mem_prod.1 (born.1 old)).1, old⟩

theorem fixedTopLayerWitness_rank_lt {P : ZFSet.{u}} {o : Ordinal.{u}}
    (limit : Order.IsSuccLimit o) (points : ZFSet.rank P < o) :
    ZFSet.rank (fixedTopLayerWitness P) < o :=
  countableLayerWitness_rank_lt limit (rank_singleton_lt limit points)
    (rank_singleton_lt limit (rank_orderedPair_lt limit points
      (by simpa only [ZFSet.rank_empty] using limit.pos)))

end

end PartitionPilot.Forcing

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

theorem transitionGraph_rank_le_code : ZFSet.rank run.transitionGraph ≤ ZFSet.rank run.code := by
  simpa only [code, Fin.cases_zero, Fin.cases_succ] using
    (rank_nonemptyTupleCode_field_le 2
      (Fin.cases run.indices (Fin.cases run.stageGraph (fun _ => run.transitionGraph))) (0 : Fin 1).succ.succ)

theorem linkedCode_rank_lt_code (i : I) : ZFSet.rank (run.linked i).code < ZFSet.rank run.code :=
  (ZFSet.rank_lt_of_mem (pair_second_mem_doubleUnion ((run.stageGraph_entry i _).2 rfl))).trans_le
    (((ZFSet.rank_sUnion_le _).trans (ZFSet.rank_sUnion_le _)).trans run.stageGraph_rank_le_code)

end PartitionPilot.Forcing.GroundMainPrefix

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixConePreservation
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
variable (last : I) (greatest : ∀ i, i ≤ last)
variable (target : GroundLinkedMainStage M K Labels C D rD)
variable (step : GroundChronologicalMainTransition (run.diagram.stage last) target.main)
variable (covered : step.CoversOldBirths)

theorem appendLast_indices :
    (run.appendLast last greatest target step covered).indices = insert run.indices run.indices :=
  run.appendKey_range

theorem appendLast_linked_old (i : I) :
    (run.appendLast last greatest target step covered).linked (i : WithTop I) = run.linked i := rfl

theorem appendLast_linked_top :
    (run.appendLast last greatest target step covered).linked ⊤ = target := rfl

theorem appendLast_transition_to_top (i : I) :
    (run.appendLast last greatest target step covered).diagram.transition
      (show (i : WithTop I) ≤ ⊤ from le_top) =
      (run.diagram.transition (greatest i)).comp pairing unions powers separation step := rfl

theorem appendLast_transition_last :
    (run.appendLast last greatest target step covered).diagram.transition
      (show (last : WithTop I) ≤ ⊤ from le_top) = step := by
  rw [run.appendLast_transition_to_top last greatest target step covered last,
    run.diagram.self, GroundChronologicalMainTransition.identity_comp]

theorem appendLast_stageGraph :
    (run.appendLast last greatest target step covered).stageGraph =
      insert (ZFSet.pair run.indices target.code) run.stageGraph :=
  run.appendStageGraph_eq target

theorem appendLast_row :
    ∃ row ∈ M.sets, FunctionGraphOn (ZFSet.prod {run.indices} run.indices) row ∧
      (∀ i z, ZFSet.pair (ZFSet.pair run.indices (run.key i)) z ∈ row ↔
        z = ((run.diagram.transition (greatest i)).comp pairing unions powers separation step).map.code) ∧
      (run.appendLast last greatest target step covered).transitionGraph =
        insert (ZFSet.pair (ZFSet.pair run.indices run.indices)
          (GroundChronologicalMainTransition.identity pairing unions powers separation target.main).map.code)
          (run.transitionGraph ∪ row) := by
  let witnesses := run.exists_appendRow last greatest target step
  have spec := Classical.choose_spec witnesses
  refine ⟨Classical.choose witnesses, spec.1, spec.2.1, spec.2.2, ?_⟩
  exact run.appendTransitionGraph_eq target (run.diagram.coneOfLast last greatest step) spec.2.1 spec.2.2

theorem appendLast_stageGraph_restrict :
    graphRestriction run.indices (run.appendLast last greatest target step covered).stageGraph = run.stageGraph := by
  rw [run.appendLast_stageGraph last greatest target step covered]
  rw [graphRestriction_insert_of_not_mem
    (fun h => (lt_irrefl _ (ZFSet.rank_lt_of_mem h)) : run.indices ∉ run.indices)]
  exact run.stageGraph_function.restriction_eq

theorem appendLast_transitionGraph_restrict :
    graphRestriction (chronologyPairs run.indices)
      (run.appendLast last greatest target step covered).transitionGraph = run.transitionGraph := by
  let extended := run.appendLast last greatest target step covered
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨key, keyMember, value, rfl, entry⟩ := mem_graphRestriction.1 hz
    obtain ⟨j, hj, i, hi, rfl, before⟩ := (mem_chronologyPairs run.indices key).1 keyMember
    obtain ⟨j, rfl⟩ := ZFSet.mem_range.1 hj
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hi
    have ordered := (run.key_order i j).2 before
    have equal := (extended.transitionGraph_entry (WithTop.coe_le_coe.mpr ordered) value).1 entry
    exact (run.transitionGraph_entry ordered value).2 equal
  · intro hz
    obtain ⟨⟨⟨i, j⟩, before⟩, rfl⟩ := (mem_familyCodeGraph _ _ _).1 hz
    exact pair_mem_graphRestriction.2
      ⟨(extended.transitionGraph_entry (WithTop.coe_le_coe.mpr before) _).2 rfl,
        (pair_mem_chronologyPairs _ _ _).2 ⟨ZFSet.mem_range.2 ⟨j, rfl⟩,
          ZFSet.mem_range.2 ⟨i, rfl⟩, (run.key_order i j).1 before⟩⟩

end PartitionPilot.Forcing.GroundMainPrefix

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u v

namespace GroundMainPrefix
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem appendSourceBound_rank_le : ZFSet.rank run.appendSourceBound ≤ ZFSet.rank run.code :=
  ((ZFSet.rank_sUnion_le _).trans ((ZFSet.rank_sUnion_le _).trans
    ((ZFSet.rank_sUnion_le _).trans ((ZFSet.rank_sUnion_le _).trans
      ((ZFSet.rank_sUnion_le _).trans ((ZFSet.rank_sUnion_le _).trans
        (ZFSet.rank_sUnion_le _))))))).trans run.transitionGraph_rank_le_code

variable (last : I) (greatest : ∀ i, i ≤ last)
variable (target : GroundLinkedMainStage M K Labels C D rD)
variable (step : GroundChronologicalMainTransition (run.diagram.stage last) target.main)

theorem appendRow_subset {row : ZFSet.{u}}
    (function : FunctionGraphOn (ZFSet.prod {run.indices} run.indices) row)
    (entries : ∀ i z, ZFSet.pair (ZFSet.pair run.indices (run.key i)) z ∈ row ↔
      z = ((run.diagram.transition (greatest i)).comp pairing unions powers separation step).map.code) :
    row ⊆ ZFSet.prod (ZFSet.prod {run.indices} run.indices)
      (ZFSet.prod (ZFSet.powerset (ZFSet.prod run.appendSourceBound target.main.stage.carrier))
        (ZFSet.powerset (ZFSet.prod run.appendSourceBound target.main.stage.actors))) := by
  have pointBound (i : I) :
      ((run.diagram.transition (greatest i)).comp pairing unions powers separation step).map.points ⊆
        ZFSet.prod run.appendSourceBound target.main.stage.carrier := by
    intro z hz
    obtain ⟨x, _, y, _, w, hw, rfl, xy, _⟩ := (mem_relationCompose _ _ _ _ _ z).1 hz
    have old := (run.transitionGraph_entry (greatest i) _).2 rfl
    have mapMem := pair_first_mem_doubleUnion (pair_second_mem_doubleUnion old)
    exact ZFSet.pair_mem_prod.2
      ⟨pair_first_mem_doubleUnion (ZFSet.mem_sUnion.2 ⟨_, mapMem, xy⟩), hw⟩
  have actorBound (i : I) :
      ((run.diagram.transition (greatest i)).comp pairing unions powers separation step).map.actors ⊆
        ZFSet.prod run.appendSourceBound target.main.stage.actors := by
    intro z hz
    obtain ⟨x, _, y, _, w, hw, rfl, xy, _⟩ := (mem_relationCompose _ _ _ _ _ z).1 hz
    have old := (run.transitionGraph_entry (greatest i) _).2 rfl
    have mapMem := pair_second_mem_doubleUnion (pair_second_mem_doubleUnion old)
    exact ZFSet.pair_mem_prod.2
      ⟨pair_first_mem_doubleUnion (ZFSet.mem_sUnion.2 ⟨_, mapMem, xy⟩), hw⟩
  intro z hz
  obtain ⟨key, keyMember, value, rfl⟩ := function.shape _ hz
  obtain ⟨a, ha, x, hx, rfl⟩ := ZFSet.mem_prod.1 keyMember
  have equal := ZFSet.mem_singleton.1 ha
  subst a
  obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hx
  have valueEq := (entries i value).1 hz
  rw [valueEq]
  exact ZFSet.pair_mem_prod.2
    ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_singleton.2 rfl, ZFSet.mem_range.2 ⟨i, rfl⟩⟩,
      ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_powerset.2 (pointBound i), ZFSet.mem_powerset.2 (actorBound i)⟩⟩

theorem appendRow_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (oldRank : ZFSet.rank run.code < o) (targetRank : ZFSet.rank target.code < o)
    {row : ZFSet.{u}} (function : FunctionGraphOn (ZFSet.prod {run.indices} run.indices) row)
    (entries : ∀ i z, ZFSet.pair (ZFSet.pair run.indices (run.key i)) z ∈ row ↔
      z = ((run.diagram.transition (greatest i)).comp pairing unions powers separation step).map.code) :
    ZFSet.rank row < o := by
  have indexRank := run.indices_rank_le_code.trans_lt oldRank
  have sourceRank := run.appendSourceBound_rank_le.trans_lt oldRank
  have pointRank : ZFSet.rank target.main.stage.carrier < o :=
    (target.field_rank_le_linkedCode 0).trans_lt targetRank
  have actorRank : ZFSet.rank target.main.stage.actors < o :=
    (target.field_rank_le_linkedCode 3).trans_lt targetRank
  have points : ZFSet.rank (ZFSet.powerset (ZFSet.prod run.appendSourceBound target.main.stage.carrier)) < o := by
    rw [ZFSet.rank_powerset]
    exact limit.succ_lt (rank_product_lt limit sourceRank pointRank)
  have actors : ZFSet.rank (ZFSet.powerset (ZFSet.prod run.appendSourceBound target.main.stage.actors)) < o := by
    rw [ZFSet.rank_powerset]
    exact limit.succ_lt (rank_product_lt limit sourceRank actorRank)
  exact (ZFSet.rank_mono (run.appendRow_subset last greatest target step function entries)).trans_lt
    (rank_product_lt limit (rank_product_lt limit (rank_singleton_lt limit indexRank) indexRank)
      (rank_product_lt limit points actors))

theorem appendLast_code_rank_lt (covered : step.CoversOldBirths)
    {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (oldRank : ZFSet.rank run.code < o) (targetRank : ZFSet.rank target.code < o) :
    ZFSet.rank (run.appendLast last greatest target step covered).code < o := by
  let extended := run.appendLast last greatest target step covered
  have indexRank := run.indices_rank_le_code.trans_lt oldRank
  have newIndices : ZFSet.rank extended.indices < o := by
    rw [run.appendLast_indices last greatest target step covered, ZFSet.rank_insert]
    exact max_lt (limit.succ_lt indexRank) indexRank
  have newStages : ZFSet.rank extended.stageGraph < o := by
    rw [run.appendLast_stageGraph last greatest target step covered, ZFSet.rank_insert]
    exact max_lt (limit.succ_lt (rank_orderedPair_lt limit indexRank targetRank))
      (run.stageGraph_rank_le_code.trans_lt oldRank)
  have newTransitions : ZFSet.rank extended.transitionGraph < o := by
    obtain ⟨row, _, function, entries, equal⟩ := run.appendLast_row last greatest target step covered
    rw [equal, ZFSet.rank_insert, ZFSet.rank_union]
    have pointRank : ZFSet.rank target.main.stage.carrier < o :=
      (target.field_rank_le_linkedCode 0).trans_lt targetRank
    have actorRank : ZFSet.rank target.main.stage.actors < o :=
      (target.field_rank_le_linkedCode 3).trans_lt targetRank
    have identityRank := (GroundChronologicalMainTransition.identity pairing unions powers separation target.main).map.code_rank_lt
      limit pointRank pointRank actorRank actorRank
    exact max_lt (limit.succ_lt (rank_orderedPair_lt limit (rank_orderedPair_lt limit indexRank indexRank) identityRank))
      (max_lt (run.transitionGraph_rank_le_code.trans_lt oldRank)
        (run.appendRow_rank_lt last greatest target step limit oldRank targetRank function entries))
  exact rank_nonemptyTupleCode_lt limit 2 _
    (Fin.cases newIndices (Fin.cases newStages (fun _ => newTransitions)))

end GroundMainPrefix
end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)
variable (target : GroundLinkedMainStage M K Labels C D rD) (cone : run.diagram.Cone target.main)
variable {row : ZFSet.{u}} (ground : row ∈ M.sets)
variable (function : FunctionGraphOn (ZFSet.prod {run.indices} run.indices) row)
variable (entries : ∀ i z, ZFSet.pair (ZFSet.pair run.indices (run.key i)) z ∈ row ↔ z = (cone.leg i).map.code)
variable (covered : cone.append.CoversOldBirths)

theorem appendCone_indices :
    (run.appendCone target cone ground function entries covered).indices = insert run.indices run.indices :=
  run.appendKey_range

theorem appendCone_linked_old (i : I) :
    (run.appendCone target cone ground function entries covered).linked (i : WithTop I) = run.linked i := rfl

theorem appendCone_linked_top :
    (run.appendCone target cone ground function entries covered).linked ⊤ = target := rfl

theorem appendCone_stageGraph :
    (run.appendCone target cone ground function entries covered).stageGraph =
      insert (ZFSet.pair run.indices target.code) run.stageGraph :=
  run.appendStageGraph_eq target

theorem appendCone_transitionGraph :
    (run.appendCone target cone ground function entries covered).transitionGraph =
      insert (ZFSet.pair (ZFSet.pair run.indices run.indices)
        (GroundChronologicalMainTransition.identity pairing unions powers separation target.main).map.code)
        (run.transitionGraph ∪ row) :=
  run.appendTransitionGraph_eq target cone function entries

theorem appendCone_stageGraph_restrict :
    graphRestriction run.indices (run.appendCone target cone ground function entries covered).stageGraph =
      run.stageGraph := by
  rw [run.appendCone_stageGraph target cone ground function entries covered]
  rw [graphRestriction_insert_of_not_mem (ZFSet.mem_irrefl run.indices)]
  exact run.stageGraph_function.restriction_eq

theorem appendCone_transitionGraph_restrict :
    graphRestriction (chronologyPairs run.indices)
      (run.appendCone target cone ground function entries covered).transitionGraph = run.transitionGraph := by
  let extended := run.appendCone target cone ground function entries covered
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨key, keyMember, value, rfl, entry⟩ := mem_graphRestriction.1 hz
    obtain ⟨j, hj, i, hi, rfl, before⟩ := (mem_chronologyPairs run.indices key).1 keyMember
    obtain ⟨j, rfl⟩ := ZFSet.mem_range.1 hj
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hi
    have ordered := (run.key_order i j).2 before
    have equal := (extended.transitionGraph_entry (WithTop.coe_le_coe.mpr ordered) value).1 entry
    exact (run.transitionGraph_entry ordered value).2 equal
  · intro hz
    obtain ⟨⟨⟨i, j⟩, before⟩, rfl⟩ := (mem_familyCodeGraph _ _ _).1 hz
    exact pair_mem_graphRestriction.2
      ⟨(extended.transitionGraph_entry (WithTop.coe_le_coe.mpr before) _).2 rfl,
        (pair_mem_chronologyPairs _ _ _).2 ⟨ZFSet.mem_range.2 ⟨j, rfl⟩,
          ZFSet.mem_range.2 ⟨i, rfl⟩, (run.key_order i j).1 before⟩⟩

theorem appendCone_code_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (oldRank : ZFSet.rank run.code < o) (targetRank : ZFSet.rank target.code < o)
    (rowRank : ZFSet.rank row < o) :
    ZFSet.rank (run.appendCone target cone ground function entries covered).code < o := by
  let extended := run.appendCone target cone ground function entries covered
  have indexRank := run.indices_rank_le_code.trans_lt oldRank
  have newIndices : ZFSet.rank extended.indices < o := by
    rw [run.appendCone_indices target cone ground function entries covered, ZFSet.rank_insert]
    exact max_lt (limit.succ_lt indexRank) indexRank
  have newStages : ZFSet.rank extended.stageGraph < o := by
    rw [run.appendCone_stageGraph target cone ground function entries covered, ZFSet.rank_insert]
    exact max_lt (limit.succ_lt (rank_orderedPair_lt limit indexRank targetRank))
      (run.stageGraph_rank_le_code.trans_lt oldRank)
  have newTransitions : ZFSet.rank extended.transitionGraph < o := by
    rw [run.appendCone_transitionGraph target cone ground function entries covered,
      ZFSet.rank_insert, ZFSet.rank_union]
    have pointRank : ZFSet.rank target.main.stage.carrier < o :=
      (target.field_rank_le_linkedCode 0).trans_lt targetRank
    have actorRank : ZFSet.rank target.main.stage.actors < o :=
      (target.field_rank_le_linkedCode 3).trans_lt targetRank
    have identityRank := (GroundChronologicalMainTransition.identity pairing unions powers separation target.main).map.code_rank_lt
      limit pointRank pointRank actorRank actorRank
    exact max_lt (limit.succ_lt (rank_orderedPair_lt limit (rank_orderedPair_lt limit indexRank indexRank) identityRank))
      (max_lt (run.transitionGraph_rank_le_code.trans_lt oldRank) rowRank)
  exact rank_nonemptyTupleCode_lt limit 2 _
    (Fin.cases newIndices (Fin.cases newStages (fun _ => newTransitions)))

end PartitionPilot.Forcing.GroundMainPrefix

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundLinkedTransitionRetarget
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

namespace LinkedMainTransitionRawCode
variable {M : TransitiveGround.{u}}
variable {K Labels C D rD N sourceCode targetCode z points actors sourceBirth targetBirth : ZFSet.{u}}
variable {source target : Fin 24 → ZFSet.{u}}

theorem exists_transition
    (raw : LinkedMainTransitionRawCode M K Labels C D rD N sourceCode targetCode z points actors
      sourceBirth targetBirth source target)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (sourceGround : ∀ j, source j ∈ M.sets) (targetGround : ∀ j, target j ∈ M.sets)
    (hPoints : points ∈ M.sets) (hActors : actors ∈ M.sets)
    (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) (omega : N = ZFSet.omega) :
    LinkedMainTransitionCode M K Labels C D rD sourceCode targetCode z := by
  obtain ⟨s, hs, sf⟩ := raw.1.exists_linked_fields pairing unions powers separation sourceGround hC hD hrD omega
  obtain ⟨t, ht, tf⟩ := raw.2.1.exists_linked_fields pairing unions powers separation targetGround hC hD hrD omega
  obtain ⟨sb, tb, ⟨encoded, ordinary, chronological⟩, coverage⟩ := raw.2.2
  rw [← sf] at sb coverage
  rw [← tf] at tb
  rw [← sf, ← tf] at ordinary chronological
  change ZFSet.pair s.main.cutoff sourceBirth ∈ s.serial.fields.graph 3 at sb
  change ZFSet.pair t.main.cutoff targetBirth ∈ t.serial.fields.graph 3 at tb
  have sourceEq : sourceBirth = s.main.birth :=
    (s.serial.fields.value_eq_of_entry 3 sb).symm.trans s.terminal_values.2.2.2.1
  have targetEq : targetBirth = t.main.birth :=
    (t.serial.fields.value_eq_of_entry 3 tb).symm.trans t.terminal_values.2.2.2.1
  rw [s.rawFields_graphs, t.rawFields_graphs, sourceEq, targetEq] at chronological
  rw [targetEq] at coverage
  let map : GroundMainTransition s.main.stage t.main.stage :=
    GroundMainTransition.ofLaws hPoints hActors ordinary
  let transition := GroundChronologicalMainTransition.ofFieldLaws s.serial.fields t.serial.fields
    s.agreement t.agreement map chronological
  exact ⟨s, t, hs, ht, transition, encoded.symm, coverage⟩

end LinkedMainTransitionRawCode

namespace GroundLinkedMainStage
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable (source target : GroundLinkedMainStage M K Labels C D rD)

theorem transition_rawFields
    (transition : GroundChronologicalMainTransition source.main target.main)
    (coverage : transition.CoversOldBirths) :
    LinkedMainTransitionRawCode M K Labels C D rD ZFSet.omega source.code target.code
      transition.map.code transition.map.points transition.map.actors source.main.birth target.main.birth
      source.rawFields target.rawFields := by
  refine ⟨source.rawFields_code, target.rawFields_code, ?_, ?_, ⟨rfl, transition.map.laws, ?_⟩, coverage⟩
  · change ZFSet.pair source.main.cutoff source.main.birth ∈ source.serial.fields.graph 3
    rw [← source.terminal_values.2.2.2.1]
    exact source.serial.fields.value_entry 3 (ZFSet.mem_insert _ _)
  · change ZFSet.pair target.main.cutoff target.main.birth ∈ target.serial.fields.graph 3
    rw [← target.terminal_values.2.2.2.1]
    exact target.serial.fields.value_entry 3 (ZFSet.mem_insert _ _)
  · rw [source.rawFields_graphs, target.rawFields_graphs]
    exact transition.field_laws source.serial.fields target.serial.fields source.agreement target.agreement

end GroundLinkedMainStage

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
include pairing unions powers separation collection

theorem realize_linkedMainTransitionFormula_raw {n} (K Labels C D rD N sourceCode targetCode z : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (linkedMainTransitionFormula K Labels C D rD N sourceCode targetCode z) env ↔
      ∃ fields : Fin 52 → ZFSet.{u}, (∀ j, fields j ∈ M.sets) ∧
        LinkedMainTransitionRawCode M (env K) (env Labels) (env C) (env D) (env rD) (env N)
          (env sourceCode) (env targetCode) (env z) (fields 48) (fields 49) (fields 50) (fields 51)
          (fun j => fields (j.castAdd 28)) (fun j => fields (Fin.natAdd 24 (j.castAdd 4))) := by
  rw [linkedMainTransitionFormula, realize_exBlock]
  have actual (fields : Fin 52 → ZFSet.{u}) (ground : ∀ j, fields j ∈ M.sets) :=
    M.realize_linkedMainTransitionRawFormula pairing unions powers separation collection
      (suffixIndex n 52 K) (suffixIndex n 52 Labels) (suffixIndex n 52 C) (suffixIndex n 52 D)
      (suffixIndex n 52 rD) (suffixIndex n 52 N) (suffixIndex n 52 sourceCode)
      (suffixIndex n 52 targetCode) (suffixIndex n 52 z)
      (prefixIndex n 52 48) (prefixIndex n 52 49) (prefixIndex n 52 50) (prefixIndex n 52 51)
      (fun j => prefixIndex n 52 (j.castAdd 28)) (fun j => prefixIndex n 52 (Fin.natAdd 24 (j.castAdd 4)))
      (extendMany 52 fields env) (extendMany_members 52 fields env ground members)
      (by simpa only [extendMany_suffix] using omega)
      (by simpa only [extendMany_suffix] using ordinal)
  simp only [extendMany_prefix, extendMany_suffix] at actual
  constructor
  · rintro ⟨fields, ground, recognized⟩
    exact ⟨fields, ground, (actual fields ground).1 recognized⟩
  · rintro ⟨fields, ground, raw⟩
    exact ⟨fields, ground, (actual fields ground).2 raw⟩

theorem realize_linkedMainTransitionFormula {n} (K Labels C D rD N sourceCode targetCode z : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (linkedMainTransitionFormula K Labels C D rD N sourceCode targetCode z) env ↔
      LinkedMainTransitionCode M (env K) (env Labels) (env C) (env D) (env rD)
        (env sourceCode) (env targetCode) (env z) := by
  rw [M.realize_linkedMainTransitionFormula_raw pairing unions powers separation collection
    K Labels C D rD N sourceCode targetCode z env members omega ordinal]
  constructor
  · rintro ⟨fields, ground, raw⟩
    exact raw.exists_transition pairing unions powers separation
      (fun j => ground (j.castAdd 28)) (fun j => ground (Fin.natAdd 24 (j.castAdd 4)))
      (ground 48) (ground 49) (members C) (members D) (members rD) omega
  · rintro ⟨source, target, sourceEq, targetEq, transition, codeEq, coverage⟩
    let extra : Fin 4 → ZFSet.{u} := Fin.cases transition.map.points (Fin.cases transition.map.actors
      (Fin.cases source.main.birth (fun _ => target.main.birth)))
    let fields : Fin 52 → ZFSet.{u} := Fin.addCases (m := 24) (n := 28) source.rawFields (Fin.addCases (m := 24) (n := 4) target.rawFields extra)
    have extraGround : ∀ j, extra j ∈ M.sets :=
      Fin.cases transition.map.points_ground (Fin.cases transition.map.actors_ground
        (Fin.cases source.main.birth_ground (fun _ => target.main.birth_ground)))
    have grounded : ∀ j, fields j ∈ M.sets := by
      intro j
      refine Fin.addCases (m := 24) (n := 28) ?_ ?_ j
      · intro k
        simpa only [fields, Fin.addCases_left] using source.rawFields_ground pairing k
      · intro k
        refine Fin.addCases (m := 24) (n := 4) ?_ ?_ k
        · intro a
          simpa only [fields, Fin.addCases_right, Fin.addCases_left] using target.rawFields_ground pairing a
        · intro a
          simpa only [fields, Fin.addCases_right] using extraGround a
    refine ⟨fields, grounded, ?_⟩
    have smap : (fun j : Fin 24 => fields (j.castAdd 28)) = source.rawFields := by
      funext j
      simp only [fields, Fin.addCases_left]
    have tmap : (fun j : Fin 24 => fields (Fin.natAdd 24 (j.castAdd 4))) = target.rawFields := by
      funext j
      simp only [fields, Fin.addCases_right, Fin.addCases_left]
    rw [smap, tmap, omega]
    change LinkedMainTransitionRawCode M (env K) (env Labels) (env C) (env D) (env rD) ZFSet.omega
      (env sourceCode) (env targetCode) (env z) transition.map.points transition.map.actors
      source.main.birth target.main.birth source.rawFields target.rawFields
    rw [← sourceEq, ← targetEq, ← codeEq]
    exact source.transition_rawFields target transition coverage

end TransitiveGround
end

universe u

end PartitionPilot.Forcing

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

namespace GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem linked_transition_code {i j : I} (before : i ≤ j) :
    LinkedMainTransitionCode M K Labels C D rD (run.linked i).code (run.linked j).code
      (run.diagram.transition before).map.code := by
  refine ⟨run.linked i, run.linked j, rfl, rfl, ?_⟩
  rw [run.linked_main i, run.linked_main j]
  exact ⟨run.diagram.transition before, rfl, run.coverage before⟩

theorem stageGraph_valid {i a : ZFSet.{u}} (entry : ZFSet.pair i a ∈ run.stageGraph) :
    ∃ linked : GroundLinkedMainStage M K Labels C D rD, linked.code = a := by
  obtain ⟨j, rfl⟩ := ZFSet.mem_range.1 (run.stageGraph_function.pair_source entry)
  exact ⟨run.linked j, ((run.stageGraph_entry j a).1 entry).symm⟩

theorem transitionGraph_valid {i j a b z : ZFSet.{u}}
    (first : ZFSet.pair i a ∈ run.stageGraph) (second : ZFSet.pair j b ∈ run.stageGraph)
    (entry : ZFSet.pair (ZFSet.pair j i) z ∈ run.transitionGraph) :
    LinkedMainTransitionCode M K Labels C D rD a b z := by
  obtain ⟨s, rfl⟩ := ZFSet.mem_range.1 (run.stageGraph_function.pair_source first)
  obtain ⟨t, rfl⟩ := ZFSet.mem_range.1 (run.stageGraph_function.pair_source second)
  have order := ((pair_mem_chronologyPairs _ _ _).1
    (run.transitionGraph_function.pair_source entry)).2.2
  have before := (run.key_order s t).2 order
  rw [(run.stageGraph_entry s a).1 first, (run.stageGraph_entry t b).1 second,
    (run.transitionGraph_entry before z).1 entry]
  exact run.linked_transition_code before

theorem transitionGraph_identity {i p a : ZFSet.{u}}
    (entry : ZFSet.pair (ZFSet.pair i i) (ZFSet.pair p a) ∈ run.transitionGraph) :
    GraphDiagonalCode p ∧ GraphDiagonalCode a := by
  have domain := (pair_mem_chronologyPairs _ _ _).1 (run.transitionGraph_function.pair_source entry)
  obtain ⟨j, rfl⟩ := ZFSet.mem_range.1 domain.1
  have equal := (run.transitionGraph_entry (le_refl j) (ZFSet.pair p a)).1 entry
  rw [run.diagram.self] at equal
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
  exact ⟨graphDiagonalCode_identity _, graphDiagonalCode_identity _⟩

theorem transitionGraph_composition {i j k p₁ a₁ p₂ a₂ p₃ a₃ : ZFSet.{u}}
    (first : ZFSet.pair (ZFSet.pair j i) (ZFSet.pair p₁ a₁) ∈ run.transitionGraph)
    (second : ZFSet.pair (ZFSet.pair k j) (ZFSet.pair p₂ a₂) ∈ run.transitionGraph)
    (third : ZFSet.pair (ZFSet.pair k i) (ZFSet.pair p₃ a₃) ∈ run.transitionGraph) :
    GraphCompositionCode p₁ p₂ p₃ ∧ GraphCompositionCode a₁ a₂ a₃ := by
  have domain₁ := (pair_mem_chronologyPairs _ _ _).1 (run.transitionGraph_function.pair_source first)
  have domain₂ := (pair_mem_chronologyPairs _ _ _).1 (run.transitionGraph_function.pair_source second)
  obtain ⟨s, rfl⟩ := ZFSet.mem_range.1 domain₁.2.1
  obtain ⟨t, rfl⟩ := ZFSet.mem_range.1 domain₁.1
  obtain ⟨v, rfl⟩ := ZFSet.mem_range.1 domain₂.1
  have before₁ := (run.key_order s t).2 domain₁.2.2
  have before₂ := (run.key_order t v).2 domain₂.2.2
  have equal₁ := (run.transitionGraph_entry before₁ _).1 first
  have equal₂ := (run.transitionGraph_entry before₂ _).1 second
  have equal₃ := (run.transitionGraph_entry (le_trans before₁ before₂) _).1 third
  rw [run.diagram.comp before₁ before₂] at equal₃
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal₁
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal₂
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal₃
  exact ⟨graphCompositionCode_relationCompose
      (run.diagram.transition before₁).map.point_embedding.injection.function
      (run.diagram.transition before₂).map.point_embedding.injection.function,
    graphCompositionCode_relationCompose
      (run.diagram.transition before₁).map.group_embedding.injection.function
      (run.diagram.transition before₂).map.group_embedding.injection.function⟩

theorem graph_code : MainPrefixGraphCode M K Labels C D rD run.indices run.stageGraph run.transitionGraph where
  ordinal := run.indices_ordinal
  stages := run.stageGraph_function
  transitions := run.transitionGraph_function
  stage_valid := fun _ _ entry => run.stageGraph_valid entry
  transition_valid := fun _ _ _ _ _ first second entry => run.transitionGraph_valid first second entry
  identity := fun _ _ _ entry => run.transitionGraph_identity entry
  composition := fun _ _ _ _ _ _ _ _ _ first second third => run.transitionGraph_composition first second third

end GroundMainPrefix

section
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

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

theorem FunctionGraphOn.restriction_eq_of_subset {A B f g : ZFSet.{u}}
    (first : FunctionGraphOn A f) (second : FunctionGraphOn B g) (subset : f ⊆ g) :
    graphRestriction A g = f := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, y, rfl, entry⟩ := mem_graphRestriction.1 hz
    obtain ⟨w, old⟩ := first.total hx
    have equal := second.unique entry (subset old)
    exact equal.symm ▸ old
  · intro hz
    obtain ⟨x, hx, y, rfl⟩ := first.shape _ hz
    exact pair_mem_graphRestriction.2 ⟨subset hz, hx⟩

theorem mainPrefixExtends_iff_restrictions
    {M : TransitiveGround.{u}} {K Labels C D rD T S E T' S' E' : ZFSet.{u}}
    (old : MainPrefixGraphCode M K Labels C D rD T S E)
    (next : MainPrefixGraphCode M K Labels C D rD T' S' E') :
    MainPrefixExtends (mainPrefixCode T S E) (mainPrefixCode T' S' E') ↔
      T ⊆ T' ∧ graphRestriction T S' = S ∧ graphRestriction (chronologyPairs T) E' = E := by
  rw [mainPrefixExtends_iff]
  constructor
  · rintro ⟨indices, stages, transitions⟩
    exact ⟨indices, old.stages.restriction_eq_of_subset next.stages stages,
      old.transitions.restriction_eq_of_subset next.transitions transitions⟩
  · rintro ⟨indices, stages, transitions⟩
    exact ⟨indices, stages ▸ graphRestriction_subset T S',
      transitions ▸ graphRestriction_subset (chronologyPairs T) E'⟩

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


namespace PartitionPilot.Forcing
universe u

namespace GroundLinkedMainStage
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable (stage : GroundLinkedMainStage M K Labels C D rD)

theorem coverageFields_iff {P G cutoff : ZFSet.{u}} :
    LinkedCoverageFieldsCode stage.code P G cutoff ↔
      P = stage.main.stage.carrier ∧ G = stage.main.stage.actors ∧ cutoff = stage.main.cutoff := by
  constructor
  · rintro ⟨r, μ, m, inv, one, action, bottom, top, height, serial, equal⟩
    have outer := linkedMainStageCode_inj.1 equal
    have fields := mainStageCode_inj.1 outer.1
    exact ⟨fields.1.symm, fields.2.2.2.1.symm, outer.2.1.symm⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨stage.main.stage.order, stage.main.stage.meetGraph, stage.main.stage.multiplication,
      stage.main.stage.inverse, stage.main.stage.identity, stage.main.stage.action,
      stage.main.stage.bottom, stage.main.stage.top, stage.main.stage.height, stage.serial.code, rfl⟩

end GroundLinkedMainStage

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

namespace GroundLinkedMainStage
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable (linked : GroundLinkedMainStage M K Labels C D rD)

theorem rawFields_birth_entry :
    ZFSet.pair (linked.rawFields 11) linked.main.birth ∈ linked.rawFields 17 := by
  change ZFSet.pair linked.main.cutoff linked.main.birth ∈ linked.serial.fields.graph 3
  rw [← linked.terminal_values.2.2.2.1]
  exact linked.serial.fields.value_entry 3 (ZFSet.mem_insert _ _)

end GroundLinkedMainStage

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
variable {target : GroundChronologicalMainStage M C D rD} (cone : run.diagram.Cone target)
variable {row : ZFSet.{u}}
variable (entries : ∀ i z, ZFSet.pair (ZFSet.pair run.indices (run.key i)) z ∈ row ↔
  z = (cone.leg i).map.code)

include entries

theorem limitConeEntry_iff (i : I) {P G cutoff points actors : ZFSet.{u}} :
    MainLimitConeEntryCode run.indices run.stageGraph row (run.key i) P G cutoff points actors ↔
      P = (run.diagram.stage i).stage.carrier ∧ G = (run.diagram.stage i).stage.actors ∧
      cutoff = (run.diagram.stage i).cutoff ∧ points = (cone.leg i).map.points ∧
      actors = (cone.leg i).map.actors := by
  have fields : LinkedCoverageFieldsCode (run.linked i).code P G cutoff ↔
      P = (run.diagram.stage i).stage.carrier ∧ G = (run.diagram.stage i).stage.actors ∧
      cutoff = (run.diagram.stage i).cutoff := by
    rw [(run.linked i).coverageFields_iff, run.linked_main]
  constructor
  · rintro ⟨_, z, stageEntry, shape, mapEntry⟩
    rw [(run.stageGraph_entry i z).1 stageEntry] at shape
    obtain ⟨hp, hg, ht⟩ := fields.1 shape
    have maps := ZFSet.pair_inj.1 ((entries i _).1 mapEntry)
    exact ⟨hp, hg, ht, maps.1, maps.2⟩
  · rintro ⟨hp, hg, ht, rfl, rfl⟩
    exact ⟨ZFSet.mem_range.2 ⟨i, rfl⟩, (run.linked i).code,
      (run.stageGraph_entry i _).2 rfl, fields.2 ⟨hp, hg, ht⟩, (entries i _).2 rfl⟩

theorem limitOldPointImage_iff (x : ZFSet.{u}) :
    MainLimitOldPointImageCode run.indices run.stageGraph row x ↔
      ∃ i y, y ∈ (run.diagram.stage i).stage.carrier ∧
        ZFSet.pair y x ∈ (cone.leg i).map.points := by
  constructor
  · rintro ⟨key, P, G, cutoff, points, actors, y, entry, hy, image⟩
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 entry.1
    obtain ⟨rfl, _, _, rfl, _⟩ := (run.limitConeEntry_iff cone entries i).1 entry
    exact ⟨i, y, hy, image⟩
  · rintro ⟨i, y, hy, image⟩
    exact ⟨run.key i, _, _, _, _, _, y,
      (run.limitConeEntry_iff cone entries i).2 ⟨rfl, rfl, rfl, rfl, rfl⟩, hy, image⟩

theorem limitOldActorImage_iff (g : ZFSet.{u}) :
    MainLimitOldActorImageCode run.indices run.stageGraph row g ↔
      ∃ i h, h ∈ (run.diagram.stage i).stage.actors ∧
        ZFSet.pair h g ∈ (cone.leg i).map.actors := by
  constructor
  · rintro ⟨key, P, G, cutoff, points, actors, h, entry, hh, image⟩
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 entry.1
    obtain ⟨_, rfl, _, _, rfl⟩ := (run.limitConeEntry_iff cone entries i).1 entry
    exact ⟨i, h, hh, image⟩
  · rintro ⟨i, h, hh, image⟩
    exact ⟨run.key i, _, _, _, _, _, h,
      (run.limitConeEntry_iff cone entries i).2 ⟨rfl, rfl, rfl, rfl, rfl⟩, hh, image⟩

omit entries in
theorem limitOldCutoff_iff (t : ZFSet.{u}) :
    MainLimitOldCutoffCode run.indices run.stageGraph t ↔ t ∈ run.cutoffLimit := by
  rw [run.cutoffLimit_mem]
  constructor
  · rintro ⟨key, member, z, entry, P, G, cutoff, shape, bound⟩
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 member
    rw [(run.stageGraph_entry i z).1 entry, (run.linked i).coverageFields_iff,
      run.linked_main] at shape
    exact ⟨i, shape.2.2 ▸ bound⟩
  · rintro ⟨i, bound⟩
    refine ⟨run.key i, ZFSet.mem_range.2 ⟨i, rfl⟩, (run.linked i).code,
      (run.stageGraph_entry i _).2 rfl, (run.diagram.stage i).stage.carrier,
      (run.diagram.stage i).stage.actors, (run.diagram.stage i).cutoff, ?_, bound⟩
    rw [(run.linked i).coverageFields_iff, run.linked_main]
    exact ⟨rfl, rfl, rfl⟩

theorem limitCoverage_graph_iff :
    MainLimitCoverageGraphCode run.indices run.stageGraph row target.stage.carrier
      target.stage.actors target.stage.order target.stage.top target.cutoff target.birth ↔
    run.LimitCoverage target cone := by
  constructor
  · intro raw
    refine ⟨fun x => (raw.points x).trans (run.limitOldPointImage_iff cone entries x),
      fun g => (raw.actors g).trans (run.limitOldActorImage_iff cone entries g), ?_, ?_, raw.top_birth⟩
    · intro i x y entry
      exact raw.strict_top _ _ _ _ _ _
        ((run.limitConeEntry_iff cone entries i).2 ⟨rfl, rfl, rfl, rfl, rfl⟩) x y entry
    · exact ZFSet.ext (fun t => (raw.cutoff_mem t).trans (run.limitOldCutoff_iff t))
  · intro coverage
    refine ⟨fun x => (coverage.points x).trans (run.limitOldPointImage_iff cone entries x).symm,
      fun g => (coverage.actors g).trans (run.limitOldActorImage_iff cone entries g).symm,
      ?_, ?_, coverage.top_birth⟩
    · intro key P G t points actors entry x y image
      obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 entry.1
      obtain ⟨_, _, _, rfl, _⟩ := (run.limitConeEntry_iff cone entries i).1 entry
      exact coverage.strict_top i x y image
    · intro t
      rw [coverage.cutoff]
      exact (run.limitOldCutoff_iff t).symm

end PartitionPilot.Forcing.GroundMainPrefix

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

theorem limitPointInclusions_rank_lt : ZFSet.rank run.limitPointInclusions < o :=
  M.indexedClassInclusions_rank_lt limit run.limitPointRelation
    (run.indices_rank_le_code.trans_lt rank) (run.carrierUnion_rank_le_code.trans_lt rank)
    (run.limitPointLabels_rank_lt limit rank)

theorem limitActorInclusions_rank_lt : ZFSet.rank run.limitActorInclusions < o :=
  M.indexedClassInclusions_rank_lt limit run.limitActorRelation
    (run.indices_rank_le_code.trans_lt rank) (run.actorUnion_rank_le_code.trans_lt rank)
    (run.limitActorLabels_rank_lt limit rank)

end

section
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem exists_limitTransitionRow {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (rank : ZFSet.rank run.code < o) :
    ∃ row ∈ M.sets, FunctionGraphOn (ZFSet.prod {run.indices} run.indices) row ∧
      (∀ i z, ZFSet.pair (ZFSet.pair run.indices (run.key i)) z ∈ row ↔
        z = ZFSet.pair (run.limitPointMap i) (run.limitActorMap i)) ∧
      ZFSet.rank row < o := by
  let P := run.limitPointInclusions.sUnion.sUnion
  let A := run.limitActorInclusions.sUnion.sUnion
  let F := pairedGraph run.indices P A run.limitPointInclusions run.limitActorInclusions
  let T := ZFSet.prod {run.indices} run.indices
  let row := relationCompose T run.indices (ZFSet.prod P A)
    (productSecond {run.indices} run.indices) F
  have hP : P ∈ M.sets := M.union_mem unions (M.union_mem unions run.limitPointInclusions_ground)
  have hA : A ∈ M.sets := M.union_mem unions (M.union_mem unions run.limitActorInclusions_ground)
  have hPair := M.prod_mem pairing unions powers separation hP hA
  have hF : F ∈ M.sets := M.pairedGraph_mem pairing unions powers separation
    run.indices_ground hP hA run.limitPointInclusions_ground run.limitActorInclusions_ground
  have hSingleton : ({run.indices} : ZFSet.{u}) ∈ M.sets := by
    rw [← ZFSet.pair_eq_singleton]
    exact M.unorderedPair_mem pairing run.indices_ground run.indices_ground
  have hT : T ∈ M.sets := M.prod_mem pairing unions powers separation hSingleton run.indices_ground
  have funcF : ZFSet.IsFunc run.indices (ZFSet.prod P A) F :=
    pairedGraph_function_of_subset run.limitPointInclusions_function.to_isFunc
      run.limitActorInclusions_function.to_isFunc (fun _ h => h)
  have func : ZFSet.IsFunc T (ZFSet.prod P A) row :=
    relationCompose_function_of_subset (productSecond_function {run.indices} run.indices)
      funcF (fun _ h => h)
  refine ⟨row, M.relationCompose_mem pairing unions powers separation hT run.indices_ground hPair
    (M.productSecond_mem pairing unions powers separation hSingleton run.indices_ground) hF,
    ⟨_, func⟩, ?_, ?_⟩
  · intro i z
    have hi : run.key i ∈ run.indices := ZFSet.mem_range.2 ⟨i, rfl⟩
    have point := (run.limitPointInclusions_entry i _).2 rfl
    have actor := (run.limitActorInclusions_entry i _).2 rfl
    have value : ZFSet.pair (run.key i)
        (ZFSet.pair (run.limitPointMap i) (run.limitActorMap i)) ∈ F :=
      (pair_mem_pairedGraph _ _ _ _ _ _ _ _).2
        ⟨hi, pair_second_mem_doubleUnion point, pair_second_mem_doubleUnion actor, point, actor⟩
    have actual : ZFSet.pair (ZFSet.pair run.indices (run.key i))
        (ZFSet.pair (run.limitPointMap i) (run.limitActorMap i)) ∈ row :=
      (pair_mem_relationCompose _ _ _ _ _ _ _).2
        ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_singleton.2 rfl, hi⟩,
          (ZFSet.pair_mem_prod.1 (funcF.1 value)).2, run.key i, hi,
          (mem_productSecond _ _ _).2 ⟨run.indices, ZFSet.mem_singleton.2 rfl, run.key i, hi, rfl⟩,
          value⟩
    exact ⟨fun entry => (FunctionGraphOn.unique ⟨_, func⟩ entry actual), fun equal => equal.symm ▸ actual⟩
  · have indexRank := run.indices_rank_le_code.trans_lt rank
    have pointRank : ZFSet.rank P < o :=
      ((ZFSet.rank_sUnion_le _).trans (ZFSet.rank_sUnion_le _)).trans_lt
        (run.limitPointInclusions_rank_lt limit rank)
    have actorRank : ZFSet.rank A < o :=
      ((ZFSet.rank_sUnion_le _).trans (ZFSet.rank_sUnion_le _)).trans_lt
        (run.limitActorInclusions_rank_lt limit rank)
    exact (ZFSet.rank_mono func.1).trans_lt
      (rank_product_lt limit (rank_product_lt limit (rank_singleton_lt limit indexRank) indexRank)
        (rank_product_lt limit pointRank actorRank))

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

end PartitionPilot.Forcing.GroundMainPrefix

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





theorem limitHeightRange_mem (t : ZFSet.{u}) :
    t ∈ run.limitHeightRange ↔
      ∃ i x, x ∈ (run.diagram.stage i).stage.carrier ∧ ZFSet.pair x t ∈ (run.diagram.stage i).stage.height := by
  rw [limitHeightRange, mem_functionGraphRange]
  constructor
  · rintro ⟨q, _, entry⟩
    obtain ⟨i, x, hx, _, value⟩ := (run.limitHeight_entry q t).1 entry
    exact ⟨i, x, hx, value⟩
  · rintro ⟨i, x, hx, entry⟩
    exact ⟨run.pointPresentation.limitPoint i x, run.pointPresentation.limitPoint_mem hx,
      (run.limitHeight_at i hx t).2 entry⟩

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundInitialMainSeedSuccessorSerialization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.GroundSerializedChronology
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {s C D rD : ZFSet.{u}}
variable (serial : GroundSerializedChronology M (insert s s) C D rD)

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (newHeight : ZFSet.{u}) (hHeight : newHeight ∈ M.sets)
include pairing unions powers separation hHeight

theorem fixedTopFields_value_at (j : Fin 5) :
    (serial.fixedTopFields pairing unions powers separation newHeight hHeight).value j s =
      serial.fixedTopValues newHeight j :=
  serial.fields.replaceTerminal_value_at pairing unions separation _ _ j

theorem fixedTopFields_value_old (j : Fin 5) {t : ZFSet.{u}} (ht : t ∈ s) :
    (serial.fixedTopFields pairing unions powers separation newHeight hHeight).value j t =
      serial.fields.value j t :=
  serial.fields.replaceTerminal_value_old pairing unions separation _ _ j ht

theorem fixedTopFields_value (j : Fin 5) {t : ZFSet.{u}} (ht : t ∈ insert s s) :
    (serial.fixedTopFields pairing unions powers separation newHeight hHeight).value j t =
      appendHistoryValue s (serial.fields.value j) (serial.fixedTopValues newHeight j) t :=
  serial.fields.replaceTerminal_value pairing unions separation _ _ j ht

theorem fixedTopFields_old_entries (j : Fin 5) {t y : ZFSet.{u}} (ht : t ∈ s) :
    ZFSet.pair t y ∈ (serial.fixedTopFields pairing unions powers separation newHeight hHeight).graph j ↔
      ZFSet.pair t y ∈ serial.fields.graph j :=
  serial.fields.replaceTerminal_old_entries pairing unions separation _ _ j ht

theorem fixedTopFields_core
    (earlier : ∀ x t, ZFSet.pair x t ∈ serial.fields.value 3 s → t ∈ s)
    (heightCode : StrictLexHeightCode (fixedTopCarrier (serial.fields.value 0 s)) C D
      (fixedTopOrder (serial.fields.value 0 s) (serial.fields.value 1 s)) newHeight rD) :
    ChronologyCoreCode (insert s s)
      (serial.fixedTopFields pairing unions powers separation newHeight hHeight).bound C D rD
      (serial.fixedTopFields pairing unions powers separation newHeight hHeight).graph := by
  let fields := serial.fixedTopFields pairing unions powers separation newHeight hHeight
  refine ⟨fields.function, ?_⟩
  intro cutoff hc L r μ birth height eL er eμ eb eh
  have eqL := fields.value_eq_of_entry 0 eL
  have eqr := fields.value_eq_of_entry 1 er
  have eqμ := fields.value_eq_of_entry 2 eμ
  have eqb := fields.value_eq_of_entry 3 eb
  have eqh := fields.value_eq_of_entry 4 eh
  rw [← eqL, ← eqr, ← eqμ, ← eqb, ← eqh]
  change ChronologyPointCode (insert s s) C D rD cutoff
    ((serial.fixedTopFields pairing unions powers separation newHeight hHeight).value 0 cutoff)
    ((serial.fixedTopFields pairing unions powers separation newHeight hHeight).value 1 cutoff)
    ((serial.fixedTopFields pairing unions powers separation newHeight hHeight).value 2 cutoff)
    ((serial.fixedTopFields pairing unions powers separation newHeight hHeight).value 3 cutoff)
    ((serial.fixedTopFields pairing unions powers separation newHeight hHeight).value 4 cutoff)
  rcases ZFSet.mem_insert_iff.1 hc with equal | hc
  · subst cutoff
    rw [fixedTopFields_value_at, fixedTopFields_value_at, fixedTopFields_value_at,
      fixedTopFields_value_at, fixedTopFields_value_at]
    have point := serial.fields.decoded_point serial.core (ZFSet.mem_insert s s)
    exact ⟨fixedTopMeet_code point.meet,
      fixedTopBirth_function point.birth_function (ZFSet.mem_insert s s),
      fun x _ t entry => fixedTopBirth_bound earlier x t entry,
      fixedTopBirth_oldMeet point.meet point.birth_function earlier point.old_meet, heightCode⟩
  · rw [fixedTopFields_value_old _ _ _ _ _ _ _ 0 hc,
      fixedTopFields_value_old _ _ _ _ _ _ _ 1 hc,
      fixedTopFields_value_old _ _ _ _ _ _ _ 2 hc,
      fixedTopFields_value_old _ _ _ _ _ _ _ 3 hc,
      fixedTopFields_value_old _ _ _ _ _ _ _ 4 hc]
    exact serial.fields.decoded_point serial.core (ZFSet.mem_insert_of_mem _ hc)

end PartitionPilot.Forcing.GroundSerializedChronology



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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRankedFixedTopSerialization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

theorem terminalChronologyGraph_rank_lt {s f v : ZFSet.{u}} {o : Ordinal.{u}}
    (limit : Order.IsSuccLimit o) (time : ZFSet.rank s < o) (graph : ZFSet.rank f < o)
    (value : ZFSet.rank v < o) : ZFSet.rank (terminalChronologyGraph s f v) < o := by
  rw [terminalChronologyGraph, ZFSet.rank_insert]
  exact max_lt (limit.succ_lt (rank_orderedPair_lt limit time value))
    ((ZFSet.rank_mono (graphRestriction_subset s f)).trans_lt graph)

namespace GroundSerializedChronology
variable {M : TransitiveGround.{u}} {s C D rD : ZFSet.{u}}
variable (serial : GroundSerializedChronology M (insert s s) C D rD)
variable {o : Ordinal.{u}} (limit : Order.IsSuccLimit o) (rank : ZFSet.rank serial.code < o)
variable {newHeight : ZFSet.{u}} (height : ZFSet.rank newHeight < o)
include limit rank height

theorem fixedTopValues_rank_lt : ∀ j, ZFSet.rank (serial.fixedTopValues newHeight j) < o := by
  have value := fun j => (serial.fieldValue_rank_lt_code j (ZFSet.mem_insert s s)).trans rank
  have time := (ZFSet.rank_lt_of_mem (ZFSet.mem_insert s s)).trans_le serial.time_rank_le_code
  have points : ZFSet.rank (fixedTopCarrier (serial.fields.value 0 s)) < o := by
    rw [fixedTopCarrier, ZFSet.rank_insert]
    exact max_lt (limit.succ_lt (value 0)) (value 0)
  have meet := fixedTopMeet_code (serial.fields.decoded_point serial.core (ZFSet.mem_insert s s)).meet
  have pp := rank_product_lt limit points points
  have order := (ZFSet.rank_mono meet.order.relation).trans_lt pp
  have operation := rank_functionGraph_lt limit meet.operation pp points
  have birth : ZFSet.rank (fixedTopBirth (serial.fields.value 0 s) (serial.fields.value 3 s) s) < o := by
    rw [fixedTopBirth, ZFSet.rank_insert]
    exact max_lt (limit.succ_lt (rank_orderedPair_lt limit (value 0) (time.trans rank))) (value 3)
  exact Fin.cases points (Fin.cases order (Fin.cases operation (Fin.cases birth (fun _ => height))))

theorem fixedTopFields_graph_rank_lt
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hHeight : newHeight ∈ M.sets) (j : Fin 5) :
    ZFSet.rank ((serial.fixedTopFields pairing unions powers separation newHeight hHeight).graph j) < o :=
  terminalChronologyGraph_rank_lt limit
    (((ZFSet.rank_lt_of_mem (ZFSet.mem_insert s s)).trans_le serial.time_rank_le_code).trans rank)
    ((serial.fieldGraph_rank_le_code j).trans_lt rank)
    (serial.fixedTopValues_rank_lt limit rank height j)

end GroundSerializedChronology

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.GroundSerializedChronology
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {s C D rD : ZFSet.{u}}
variable (serial : GroundSerializedChronology M (insert s s) C D rD)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (newHeight : ZFSet.{u}) (hHeight : newHeight ∈ M.sets)
variable (ordinal : ordinalSetProperty s)
variable (earlier : ∀ x t, ZFSet.pair x t ∈ serial.fields.value 3 s → t ∈ s)
variable {o : Ordinal.{u}} (limit : Order.IsSuccLimit o) (rank : ZFSet.rank serial.code < o)
include pairing unions powers separation hHeight ordinal earlier limit rank

theorem fixedTopFields_rankedRawWitnesses :
    let fields := serial.fixedTopFields pairing unions powers separation newHeight hHeight
    ∀ cutoff ∈ insert s s, ∀ t ∈ insert s s, t = cutoff ∨ t ∈ cutoff →
      ∃ z ∈ M.sets, ZFSet.rank z < o ∧ GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
        (fields.value 0 cutoff) (fields.value 1 cutoff) (fields.value 2 cutoff)
        (fields.value 3 cutoff) t ZFSet.omega z := by
  dsimp only
  let fields := serial.fixedTopFields pairing unions powers separation newHeight hHeight
  have inside {t a : ZFSet.{u}} (ht : t ∈ insert s s) (ha : a ∈ t) : a ∈ s := by
    rcases ZFSet.mem_insert_iff.1 ht with equal | ht
    · exact equal ▸ ha
    · exact ordinal.1 t ht a ha
  have transportSources {t A r μ birth z : ZFSet.{u}} (ht : t ∈ insert s s)
      (code : GrowthLayerWitnessCode (serial.fields.graph 0) (serial.fields.graph 1) (serial.fields.graph 2)
        A r μ birth t ZFSet.omega z) :
      GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
        A r μ birth t ZFSet.omega z := by
    exact code.congr_source_entries
      (fun a ha y => (serial.fixedTopFields_old_entries pairing unions powers separation newHeight hHeight 0
        (y := y) (inside ht ha)).symm)
      (fun a ha y => (serial.fixedTopFields_old_entries pairing unions powers separation newHeight hHeight 1
        (y := y) (inside ht ha)).symm)
      (fun a ha y => (serial.fixedTopFields_old_entries pairing unions powers separation newHeight hHeight 2
        (y := y) (inside ht ha)).symm)
  intro cutoff hc t ht before
  change ∃ z ∈ M.sets, ZFSet.rank z < o ∧ GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
    (fields.value 0 cutoff) (fields.value 1 cutoff) (fields.value 2 cutoff) (fields.value 3 cutoff) t ZFSet.omega z
  by_cases terminal : cutoff = s
  · subst cutoff
    change ∃ z ∈ M.sets, ZFSet.rank z < o ∧ GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
      ((serial.fixedTopFields pairing unions powers separation newHeight hHeight).value 0 s)
      ((serial.fixedTopFields pairing unions powers separation newHeight hHeight).value 1 s)
      ((serial.fixedTopFields pairing unions powers separation newHeight hHeight).value 2 s)
      ((serial.fixedTopFields pairing unions powers separation newHeight hHeight).value 3 s) t ZFSet.omega z
    rw [fixedTopFields_value_at, fixedTopFields_value_at, fixedTopFields_value_at, fixedTopFields_value_at]
    by_cases top : t = s
    · subst t
      exact ⟨fixedTopLayerWitness (serial.fields.value 0 s),
        M.fixedTopLayerWitness_mem pairing (serial.fields.value_ground 0 s),
        fixedTopLayerWitness_rank_lt limit ((serial.fieldValue_rank_lt_code 0 (ZFSet.mem_insert s s)).trans rank),
        fixedTopLayerWitness_code earlier⟩
    · have strict : t ∈ s := before.resolve_left top
      have prior := serial.layer_code s (ZFSet.mem_insert s s) t ht (Or.inr strict)
        _ (serial.layerWitness_entry (ZFSet.mem_insert s s) ht (Or.inr strict))
      have point := serial.fields.decoded_point serial.core (ZFSet.mem_insert s s)
      obtain ⟨z, hz, code, rankZ⟩ := prior.exists_fixedTop_earlier_rank_lt pairing unions separation
        (serial.fields.value_ground 0 s) (serial.layerWitness_ground s t) limit
        ((serial.layerWitness_rank_lt_code (ZFSet.mem_insert s s) ht (Or.inr strict)).trans rank)
        point.meet point.birth_function strict
      exact ⟨z, hz, rankZ, transportSources ht code⟩
  · have old : cutoff ∈ s := (ZFSet.mem_insert_iff.1 hc).resolve_left terminal
    have code := transportSources ht (serial.layer_code cutoff hc t ht before
      _ (serial.layerWitness_entry hc ht before))
    refine ⟨serial.layerWitness cutoff t, serial.layerWitness_ground cutoff t,
      (serial.layerWitness_rank_lt_code hc ht before).trans rank, ?_⟩
    change GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
      ((serial.fixedTopFields pairing unions powers separation newHeight hHeight).value 0 cutoff)
      ((serial.fixedTopFields pairing unions powers separation newHeight hHeight).value 1 cutoff)
      ((serial.fixedTopFields pairing unions powers separation newHeight hHeight).value 2 cutoff)
      ((serial.fixedTopFields pairing unions powers separation newHeight hHeight).value 3 cutoff) t ZFSet.omega _
    rw [fixedTopFields_value_old _ _ _ _ _ _ _ 0 old,
      fixedTopFields_value_old _ _ _ _ _ _ _ 1 old,
      fixedTopFields_value_old _ _ _ _ _ _ _ 2 old,
      fixedTopFields_value_old _ _ _ _ _ _ _ 3 old]
    exact code

end PartitionPilot.Forcing.GroundSerializedChronology

namespace PartitionPilot.Forcing.GroundSerializedChronology
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {s C D rD K : ZFSet.{u}}
variable (serial : GroundSerializedChronology M (insert s s) C D rD)

theorem exists_rankedFixedTopSerialization
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    (time : insert s s ∈ K) (level : GroundMainCandidateLevel M K)
    (rank : ZFSet.rank serial.code < ZFSet.rank K)
    (newHeight : ZFSet.{u}) (hHeight : newHeight ∈ M.sets)
    (heightRank : ZFSet.rank newHeight < ZFSet.rank K)
    (ordinal : ordinalSetProperty s)
    (earlier : ∀ x t, ZFSet.pair x t ∈ serial.fields.value 3 s → t ∈ s)
    (heightCode : StrictLexHeightCode (fixedTopCarrier (serial.fields.value 0 s)) C D
      (fixedTopOrder (serial.fields.value 0 s) (serial.fields.value 1 s)) newHeight rD) :
    ∃ extended : GroundSerializedChronology M (insert s s) C D rD,
      extended.code ∈ M.sets ∧ ZFSet.rank extended.code < ZFSet.rank K ∧
        extended.code ∈ level.validChronologies C D rD ∧
        extended.fields.graph = (serial.fixedTopFields pairing unions powers separation newHeight hHeight).graph ∧
        ∀ j t, t ∈ insert s s → extended.fields.value j t =
          appendHistoryValue s (serial.fields.value j) (serial.fixedTopValues newHeight j) t := by
  have limit := conditions.rank_isLimit pairing unions powers separation infinite hK
  obtain ⟨extended, ground, rankExtended, member, graphs, values, _⟩ :=
    (serial.fixedTopFields pairing unions powers separation newHeight hHeight).exists_rankedSerialization
      pairing unions powers separation collection infinite choice hK conditions time level
      (ordinalSetProperty_succ ordinal)
      (serial.fixedTopFields_core pairing unions powers separation newHeight hHeight earlier heightCode)
      (serial.fixedTopFields_graph_rank_lt limit rank heightRank pairing unions powers separation hHeight)
      (serial.fixedTopFields_rankedRawWitnesses pairing unions powers separation
        newHeight hHeight ordinal earlier limit rank)
  refine ⟨extended, ground, rankExtended, member, graphs, ?_⟩
  intro j t ht
  rw [values j t]
  exact serial.fixedTopFields_value pairing unions powers separation newHeight hHeight j ht

end PartitionPilot.Forcing.GroundSerializedChronology

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

namespace TaskBearingMainSuccessorCode
variable {M : TransitiveGround.{u}} {K Labels C D rD N sourceCode targetCode z : ZFSet.{u}}

theorem linked_transition
    (code : TaskBearingMainSuccessorCode M K Labels C D rD N sourceCode targetCode z)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) (omega : N = ZFSet.omega) :
    LinkedMainTransitionCode M K Labels C D rD sourceCode targetCode z := by
  obtain ⟨fields, ground, raw⟩ := code
  exact raw.1.exists_transition pairing unions powers separation
    (fun j => ground (j.castAdd 36)) (fun j => ground (Fin.natAdd 24 (j.castAdd 12)))
    (ground 48) (ground 49) hC hD hrD omega

end TaskBearingMainSuccessorCode

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

theorem old_profiles_on_linked
    (code : TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega
      source.code target.code transition.map.code) :
    OldProfilePreservationCode source.main.stage.carrier source.main.stage.order source.main.stage.meetGraph
      target.main.stage.carrier target.main.stage.order target.main.stage.meetGraph
      transition.map.points (M.groundPower source.main.stage.carrier) := by
  obtain ⟨extra, _, output, bindings⟩ := code.output_on_linked
  have families := bindings.2.2.2.2.2.1
  have preservation := output.old_profiles
  rw [families] at preservation
  exact preservation

end PartitionPilot.Forcing.TaskBearingMainSuccessorCode



namespace PartitionPilot.Forcing.TaskBearingMainSuccessorCode
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {K Labels C D rD targetCode z : ZFSet.{u}}
variable {source : GroundLinkedMainStage M K Labels C D rD}

theorem exists_from_linked
    (code : TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega source.code targetCode z)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets) :
    ∃ target : GroundLinkedMainStage M K Labels C D rD, target.code = targetCode ∧
      ∃ transition : GroundChronologicalMainTransition source.main target.main,
        transition.map.code = z ∧ transition.CoversOldBirths ∧
        OldProfilePreservationCode source.main.stage.carrier source.main.stage.order source.main.stage.meetGraph
          target.main.stage.carrier target.main.stage.order target.main.stage.meetGraph
          transition.map.points (M.groundPower source.main.stage.carrier) := by
  obtain ⟨first, target, sourceEqual, targetEqual, decoded, mapEqual, covered⟩ :=
    code.linked_transition pairing unions powers separation source.main.stage.columns_ground
      source.main.stage.coordinates_ground source.main.stage.coordinate_order_ground rfl
  let transition := decoded.retargetLinked sourceEqual (rfl : target.code = target.code)
  have exactMap : transition.map.code = z :=
    (decoded.retargetLinked_code sourceEqual rfl).trans mapEqual
  have actual : TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega
      source.code target.code transition.map.code := by
    rw [targetEqual, exactMap]
    exact code
  exact ⟨target, targetEqual, transition, exactMap,
    decoded.retargetLinked_coversOldBirths sourceEqual rfl covered,
    actual.old_profiles_on_linked⟩

end PartitionPilot.Forcing.TaskBearingMainSuccessorCode

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

end TransitiveGround
end PartitionPilot.Forcing




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

theorem identity_preservesOldProfiles
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (stage : GroundChronologicalMainStage M C D rD) :
    (identity pairing unions powers separation stage).PreservesOldProfiles :=
  OldProfilePreservationCode.identity stage.stage.carrier stage.stage.order stage.stage.meetGraph
    (M.groundPower stage.stage.carrier)

theorem comp_preservesOldProfiles
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (left : GroundChronologicalMainTransition source middle)
    (right : GroundChronologicalMainTransition middle target)
    (first : left.PreservesOldProfiles) (second : right.PreservesOldProfiles) :
    (left.comp pairing unions powers separation right).PreservesOldProfiles :=
  OldProfilePreservationCode.comp_ground M separation first second middle.stage.carrier_ground
    left.map.points_ground

theorem retargetEq_preservesOldProfiles_iff
    (transition : GroundChronologicalMainTransition source target)
    (sourceEqual : source = first) (targetEqual : target = second) :
    (transition.retargetEq sourceEqual targetEqual).PreservesOldProfiles ↔ transition.PreservesOldProfiles := by
  cases sourceEqual
  cases targetEqual
  rfl

end GroundChronologicalMainTransition

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

theorem appendCone_preservesOldProfiles (preserved : run.PreservesOldProfiles)
    (target : GroundLinkedMainStage M K Labels C D rD) (cone : run.diagram.Cone target.main)
    {row : ZFSet.{u}} (ground : row ∈ M.sets)
    (function : FunctionGraphOn (ZFSet.prod {run.indices} run.indices) row)
    (entries : ∀ i z, ZFSet.pair (ZFSet.pair run.indices (run.key i)) z ∈ row ↔ z = (cone.leg i).map.code)
    (covered : cone.append.CoversOldBirths) (legs : ∀ i, (cone.leg i).PreservesOldProfiles) :
    (run.appendCone target cone ground function entries covered).PreservesOldProfiles := by
  intro i j before
  cases i with
  | top =>
    cases j with
    | top =>
      exact GroundChronologicalMainTransition.identity_preservesOldProfiles
        pairing unions powers separation target.main
    | coe j => exact False.elim (WithTop.not_top_le_coe j before)
  | coe i =>
    cases j with
    | top => exact legs i
    | coe j => exact preserved i j (WithTop.coe_le_coe.mp before)

theorem appendLast_preservesOldProfiles (preserved : run.PreservesOldProfiles)
    (last : I) (greatest : ∀ i, i ≤ last)
    (target : GroundLinkedMainStage M K Labels C D rD)
    (step : GroundChronologicalMainTransition (run.diagram.stage last) target.main)
    (covered : step.CoversOldBirths) (stepPreserved : step.PreservesOldProfiles) :
    (run.appendLast last greatest target step covered).PreservesOldProfiles := by
  intro i j before
  cases i with
  | top =>
    cases j with
    | top =>
      exact GroundChronologicalMainTransition.identity_preservesOldProfiles
        pairing unions powers separation target.main
    | coe j => exact False.elim (WithTop.not_top_le_coe j before)
  | coe i =>
    cases j with
    | top =>
      exact GroundChronologicalMainTransition.comp_preservesOldProfiles
        pairing unions powers separation (run.diagram.transition (greatest i)) step
        (preserved i last (greatest i)) stepPreserved
    | coe j => exact preserved i j (WithTop.coe_le_coe.mp before)

end PartitionPilot.Forcing.GroundMainPrefix



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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_LinkedProfileTransitionRawCodes
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
theorem realize_linkedProfilePreservingTransitionRawFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) {n}
    (K Labels C D rD N sourceCode targetCode z points actors sourceBirth targetBirth Families : Fin n)
    (source target : Fin 24 → Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (linkedProfilePreservingTransitionRawFormula K Labels C D rD N sourceCode targetCode z
      points actors sourceBirth targetBirth Families source target) env ↔
    LinkedProfilePreservingTransitionRawCode M (env K) (env Labels) (env C) (env D) (env rD)
      (env N) (env sourceCode) (env targetCode) (env z) (env points) (env actors)
      (env sourceBirth) (env targetBirth) (env Families)
      (fun j => env (source j)) (fun j => env (target j)) :=
  (M.realize_linkedMainTransitionRawFormula pairing unions powers separation collection
    K Labels C D rD N sourceCode targetCode z points actors sourceBirth targetBirth source target
    env members omega ordinal).and
    ((M.realize_relativePowerFormula (source 0) Families env members).and
      (BoundedFormula.realize_oldProfilePreservationFormula M (source 0) (source 1) (source 2)
        (target 0) (target 1) (target 2) points Families env members))

end TransitiveGround

namespace LinkedProfilePreservingTransitionRawCode
variable {M : TransitiveGround.{u}}
variable {K Labels C D rD N sourceCode targetCode z points actors sourceBirth targetBirth Families : ZFSet.{u}}
variable {source target : Fin 24 → ZFSet.{u}}

theorem exists_transition
    (raw : LinkedProfilePreservingTransitionRawCode M K Labels C D rD N sourceCode targetCode z
      points actors sourceBirth targetBirth Families source target)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (sourceGround : ∀ j, source j ∈ M.sets) (targetGround : ∀ j, target j ∈ M.sets)
    (hPoints : points ∈ M.sets) (hActors : actors ∈ M.sets)
    (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) (omega : N = ZFSet.omega) :
    LinkedProfilePreservingTransitionCode M K Labels C D rD sourceCode targetCode z := by
  rw [omega] at raw
  obtain ⟨s, t, sourceEqual, targetEqual, transition, equal, covered⟩ :=
    raw.1.exists_transition pairing unions powers separation sourceGround targetGround
      hPoints hActors hC hD hrD rfl
  have sourceCode := s.rawFields_code
  have targetCode := t.rawFields_code
  rw [sourceEqual] at sourceCode
  rw [targetEqual] at targetCode
  have sourceFields := sourceCode.fields_unique raw.1.1
  have targetFields := targetCode.fields_unique raw.1.2.1
  have mapEqual : ZFSet.pair transition.map.points transition.map.actors = ZFSet.pair points actors :=
    equal.trans raw.1.2.2.2.2.1.1
  have pointsEqual := (ZFSet.pair_inj.1 mapEqual).1
  have preservation := raw.2.2
  rw [raw.2.1, ← sourceFields, ← targetFields] at preservation
  refine ⟨s, t, sourceEqual, targetEqual, transition, equal, covered, ?_⟩
  change OldProfilePreservationCode s.main.stage.carrier s.main.stage.order s.main.stage.meetGraph
    t.main.stage.carrier t.main.stage.order t.main.stage.meetGraph
    transition.map.points (M.groundPower s.main.stage.carrier)
  rw [pointsEqual]
  exact preservation

end LinkedProfilePreservingTransitionRawCode

namespace GroundLinkedMainStage
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable (source target : GroundLinkedMainStage M K Labels C D rD)
theorem profileTransition_rawFields
    (transition : GroundChronologicalMainTransition source.main target.main)
    (covered : transition.CoversOldBirths) (preserved : transition.PreservesOldProfiles) :
    LinkedProfilePreservingTransitionRawCode M K Labels C D rD ZFSet.omega source.code target.code
      transition.map.code transition.map.points transition.map.actors source.main.birth target.main.birth
      (M.groundPower source.main.stage.carrier) source.rawFields target.rawFields :=
  ⟨source.transition_rawFields target transition covered, rfl, preserved⟩

end GroundLinkedMainStage

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_MainLimitCoverageFormulas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

theorem truth_exLinkedCoverageFields {n} (z : Fin n) (body : BoundedFormula (n + 3))
    (env : Fin n → ZFSet.{u}) :
    Truth (exLinkedCoverageFields z body) env ↔
      ∃ P G cutoff, LinkedCoverageFieldsCode (env z) P G cutoff ∧
        Truth body (extend cutoff (extend G (extend P env))) := by
  simp only [exLinkedCoverageFields, truth_exPairFields, Truth, truth_tupleShapeFormula,
    truth_reindex]
  have rearrange (s outer cutoff serial P tail r tail' μ tail'' G rest : ZFSet.{u}) :
      (fun i => extend rest (extend G (extend tail'' (extend μ (extend tail' (extend r
        (extend tail (extend P (extend serial (extend cutoff (extend outer (extend s env)))))))))))
        (Fin.cases 9 (Fin.cases 1 (Fin.cases 7
          (fun j => j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))) i)) =
        extend cutoff (extend G (extend P env)) := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.cases ?_ (fun l => ?_) k) j) i <;> rfl
  simp only [rearrange]
  change (∃ s outer, env z = ZFSet.pair s outer ∧ ∃ cutoff serial,
    outer = ZFSet.pair cutoff serial ∧ ∃ P tail, s = ZFSet.pair P tail ∧
    ∃ r tail', tail = ZFSet.pair r tail' ∧ ∃ μ tail'', tail' = ZFSet.pair μ tail'' ∧
    ∃ G rest, tail'' = ZFSet.pair G rest ∧
      (∃ fields, rest = nonemptyTupleCode 6 fields) ∧
      Truth body (extend cutoff (extend G (extend P env)))) ↔ _
  constructor
  · rintro ⟨s, outer, equal, cutoff, serial, rfl, P, tail, rfl, r, tail', rfl,
      μ, tail'', rfl, G, rest, rfl, ⟨fields, rfl⟩, holds⟩
    exact ⟨P, G, cutoff, ⟨r, μ, fields 0, fields 1, fields 2, fields 3, fields 4,
      fields 5, fields 6, serial, equal⟩, holds⟩
  · rintro ⟨P, G, cutoff, ⟨r, μ, m, inv, one, action, bottom, top, height, serial, equal⟩, holds⟩
    let fields : Fin 7 → ZFSet.{u} := Fin.cases m (Fin.cases inv (Fin.cases one
      (Fin.cases action (Fin.cases bottom (Fin.cases top (fun _ => height))))))
    refine ⟨_, _, equal, cutoff, serial, rfl, P, _, rfl, r, _, rfl, μ, _, rfl,
      G, nonemptyTupleCode 6 fields, rfl, ⟨fields, rfl⟩, holds⟩





theorem truth_exMainLimitStageFields {n} (T S : Fin n) (body : BoundedFormula (n + 4))
    (env : Fin n → ZFSet.{u}) :
    Truth (exMainLimitStageFields T S body) env ↔
      ∃ i z P G t, i ∈ env T ∧ ZFSet.pair i z ∈ env S ∧
        LinkedCoverageFieldsCode z P G t ∧ Truth body (extend t (extend G (extend P (extend i env)))) := by
  simp only [exMainLimitStageFields, truth_exGraphFields, Truth, truth_exLinkedCoverageFields,
    truth_reindex]
  have rearrange (i z P G t : ZFSet.{u}) :
      (fun j => extend t (extend G (extend P (extend z (extend i env))))
        (Fin.cases 0 (Fin.cases 1 (Fin.cases 2 (Fin.cases 4
          (fun k => k.succ.succ.succ.succ.succ)))) j)) =
        extend t (extend G (extend P (extend i env))) := by
    funext j
    refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun l => Fin.cases ?_
      (fun m => Fin.cases ?_ (fun a => ?_) m) l) k) j <;> rfl
  simp only [rearrange]
  change (∃ i z, ZFSet.pair i z ∈ env S ∧ i ∈ env T ∧ ∃ P G t,
    LinkedCoverageFieldsCode z P G t ∧ Truth body (extend t (extend G (extend P (extend i env))))) ↔ _
  constructor
  · rintro ⟨i,z,entry,member,P,G,t,shape,holds⟩
    exact ⟨i,z,P,G,t,member,entry,shape,holds⟩
  · rintro ⟨i,z,P,G,t,member,entry,shape,holds⟩
    exact ⟨i,z,entry,member,P,G,t,shape,holds⟩

theorem truth_exMainLimitConeFields {n} (T S row : Fin n) (body : BoundedFormula (n + 6))
    (env : Fin n → ZFSet.{u}) :
    Truth (exMainLimitConeFields T S row body) env ↔
      ∃ i P G t points actors, MainLimitConeEntryCode (env T) (env S) (env row) i P G t points actors ∧
        Truth body (extend actors (extend points (extend t (extend G (extend P (extend i env)))))) := by
  simp only [exMainLimitConeFields, truth_exMainLimitStageFields, truth_exGraphFields, Truth,
    truth_orderedPairFormula, truth_exPairFields, truth_reindex]
  have rearrange (i P G t key value points actors : ZFSet.{u}) :
      (fun j => extend actors (extend points (extend value (extend key (extend t
        (extend G (extend P (extend i env)))))))
        (Fin.cases 0 (Fin.cases 1 (Fin.cases 4 (Fin.cases 5 (Fin.cases 6
          (Fin.cases 7 (fun k => k.succ.succ.succ.succ.succ.succ.succ.succ)))))) j)) =
      extend actors (extend points (extend t (extend G (extend P (extend i env))))) := by
    funext j
    refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun b => Fin.cases ?_ (fun c =>
      Fin.cases ?_ (fun d => Fin.cases ?_ (fun e => Fin.cases ?_ (fun f => ?_) e) d) c) b) a) j <;> rfl
  simp only [rearrange]
  change (∃ i z P G t, i ∈ env T ∧ ZFSet.pair i z ∈ env S ∧ LinkedCoverageFieldsCode z P G t ∧
    ∃ key value, ZFSet.pair key value ∈ env row ∧ key = ZFSet.pair (env T) i ∧
    ∃ points actors, value = ZFSet.pair points actors ∧
    Truth body (extend actors (extend points (extend t (extend G (extend P (extend i env))))))) ↔ _
  constructor
  · rintro ⟨i,z,P,G,t,member,entry,shape,key,value,rowEntry,rfl,points,actors,rfl,holds⟩
    exact ⟨i,P,G,t,points,actors,⟨member,z,entry,shape,rowEntry⟩,holds⟩
  · rintro ⟨i,P,G,t,points,actors,⟨member,z,entry,shape,rowEntry⟩,holds⟩
    exact ⟨i,z,P,G,t,member,entry,shape,_,_,rowEntry,rfl,points,actors,rfl,holds⟩





theorem truth_exMainLimitImageFields {n} (actor : Bool) (T S row : Fin n)
    (body : BoundedFormula (n + 1)) (env : Fin n → ZFSet.{u}) :
    Truth (exMainLimitImageFields actor T S row body) env ↔
      ∃ x, (if actor then MainLimitOldActorImageCode (env T) (env S) (env row) x
        else MainLimitOldPointImageCode (env T) (env S) (env row) x) ∧ Truth body (extend x env) := by
  simp only [exMainLimitImageFields, truth_exMainLimitConeFields, truth_exGraphFields, Truth, truth_reindex]
  have rearrange (i P G t points actors y x : ZFSet.{u}) :
      (fun j => extend x (extend y (extend actors (extend points (extend t
        (extend G (extend P (extend i env)))))))
        (Fin.cases 0 (fun k => k.succ.succ.succ.succ.succ.succ.succ.succ) j)) = extend x env := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j <;> rfl
  simp only [rearrange]
  cases actor <;> simp only [Bool.false_eq_true, ite_false, if_false, ite_true, if_true]
  · change (∃ i P G t points actors, MainLimitConeEntryCode (env T) (env S) (env row) i P G t points actors ∧
      ∃ y x, ZFSet.pair y x ∈ points ∧ y ∈ P ∧ Truth body (extend x env)) ↔ _
    constructor
    · rintro ⟨i,P,G,t,points,actors,entry,y,x,image,member,holds⟩
      exact ⟨x,⟨i,P,G,t,points,actors,y,entry,member,image⟩,holds⟩
    · rintro ⟨x,⟨i,P,G,t,points,actors,y,entry,member,image⟩,holds⟩
      exact ⟨i,P,G,t,points,actors,entry,y,x,image,member,holds⟩
  · change (∃ i P G t points actors, MainLimitConeEntryCode (env T) (env S) (env row) i P G t points actors ∧
      ∃ y x, ZFSet.pair y x ∈ actors ∧ y ∈ G ∧ Truth body (extend x env)) ↔ _
    constructor
    · rintro ⟨i,P,G,t,points,actors,entry,y,x,image,member,holds⟩
      exact ⟨x,⟨i,P,G,t,points,actors,y,entry,member,image⟩,holds⟩
    · rintro ⟨x,⟨i,P,G,t,points,actors,y,entry,member,image⟩,holds⟩
      exact ⟨i,P,G,t,points,actors,entry,y,x,image,member,holds⟩

theorem truth_mainLimitImageFormula {n} (actor : Bool) (T S row x : Fin n)
    (env : Fin n → ZFSet.{u}) : Truth (mainLimitImageFormula actor T S row x) env ↔
      (if actor then MainLimitOldActorImageCode (env T) (env S) (env row) (env x)
        else MainLimitOldPointImageCode (env T) (env S) (env row) (env x)) := by
  rw [mainLimitImageFormula, truth_exMainLimitImageFields]
  change (∃ y, _ ∧ y = env x) ↔ _
  constructor
  · rintro ⟨y, member, rfl⟩
    exact member
  · exact fun member => ⟨env x, member, rfl⟩

theorem truth_mainLimitOldCutoffFormula {n} (T S t : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (mainLimitOldCutoffFormula T S t) env ↔ MainLimitOldCutoffCode (env T) (env S) (env t) := by
  simp only [mainLimitOldCutoffFormula, truth_exMainLimitStageFields, truth_disj, Truth]
  change (∃ i z P G cutoff, i ∈ env T ∧ ZFSet.pair i z ∈ env S ∧
    LinkedCoverageFieldsCode z P G cutoff ∧ (env t = cutoff ∨ env t ∈ cutoff)) ↔ _
  constructor
  · rintro ⟨i,z,P,G,cutoff,member,entry,shape,bound⟩
    exact ⟨i,member,z,entry,P,G,cutoff,shape,bound⟩
  · rintro ⟨i,member,z,entry,P,G,cutoff,shape,bound⟩
    exact ⟨i,z,P,G,cutoff,member,entry,shape,bound⟩





theorem truth_mainLimitPointCoverageFormula {n} (T S row Q top : Fin n)
    (env : Fin n → ZFSet.{u}) : Truth (mainLimitPointCoverageFormula T S row Q top) env ↔
      ∀ x, (x ∈ env Q ∧ x ≠ env top) ↔ MainLimitOldPointImageCode (env T) (env S) (env row) x := by
  classical
  simp only [mainLimitPointCoverageFormula, Truth, truth_imp, truth_mainLimitImageFormula,
    truth_exMainLimitImageFields, Bool.false_eq_true, ite_false, if_false, not_exists, not_and, not_not, Classical.not_imp]
  change ((∀ x ∈ env Q, x ≠ env top → MainLimitOldPointImageCode (env T) (env S) (env row) x) ∧
    ∀ x, MainLimitOldPointImageCode (env T) (env S) (env row) x → x ∈ env Q ∧ x ≠ env top) ↔ _
  constructor
  · rintro ⟨forward, reverse⟩ x
    exact ⟨fun h => forward x h.1 h.2, reverse x⟩
  · intro laws
    exact ⟨fun x member different => (laws x).1 ⟨member,different⟩, fun x => (laws x).2⟩

theorem truth_mainLimitActorCoverageFormula {n} (T S row H : Fin n)
    (env : Fin n → ZFSet.{u}) : Truth (mainLimitActorCoverageFormula T S row H) env ↔
      ∀ g, g ∈ env H ↔ MainLimitOldActorImageCode (env T) (env S) (env row) g := by
  classical
  simp only [mainLimitActorCoverageFormula, Truth, truth_mainLimitImageFormula,
    truth_exMainLimitImageFields, ite_true, if_true, not_exists, not_and, not_not]
  change ((∀ g ∈ env H, MainLimitOldActorImageCode (env T) (env S) (env row) g) ∧
    ∀ g, MainLimitOldActorImageCode (env T) (env S) (env row) g → g ∈ env H) ↔ _
  exact ⟨fun h g => ⟨h.1 g,h.2 g⟩, fun h => ⟨fun g => (h g).1,fun g => (h g).2⟩⟩

theorem truth_mainLimitStrictTopFormula {n} (T S row R top : Fin n)
    (env : Fin n → ZFSet.{u}) : Truth (mainLimitStrictTopFormula T S row R top) env ↔
      ∀ i P G t points actors, MainLimitConeEntryCode (env T) (env S) (env row) i P G t points actors →
        ∀ x y, ZFSet.pair x y ∈ points → ZFSet.pair y (env top) ∈ env R ∧
          ZFSet.pair (env top) y ∉ env R := by
  classical
  simp only [mainLimitStrictTopFormula, Truth, truth_exMainLimitConeFields,
    truth_exGraphFields, truth_pairMembershipFormula, not_exists, not_and, not_not, Classical.not_imp]
  rfl

theorem truth_mainLimitCutoffFormula {n} (T S cutoff : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (mainLimitCutoffFormula T S cutoff) env ↔
      ∀ t, t ∈ env cutoff ↔ MainLimitOldCutoffCode (env T) (env S) t := by
  classical
  simp only [mainLimitCutoffFormula, Truth, truth_mainLimitOldCutoffFormula,
    truth_exMainLimitStageFields, not_exists, not_and, not_not, Classical.not_imp]
  change ((∀ t ∈ env cutoff, MainLimitOldCutoffCode (env T) (env S) t) ∧
    ∀ i z P G t, i ∈ env T → ZFSet.pair i z ∈ env S → LinkedCoverageFieldsCode z P G t →
      t ∈ env cutoff ∧ ∀ s ∈ t, s ∈ env cutoff) ↔ _
  constructor
  · rintro ⟨forward,bound⟩ t
    refine ⟨forward t, ?_⟩
    rintro ⟨i,member,z,entry,P,G,s,shape,equal | lower⟩
    · exact equal.symm ▸ (bound i z P G s member entry shape).1
    · exact (bound i z P G s member entry shape).2 t lower
  · intro laws
    refine ⟨fun t => (laws t).1, ?_⟩
    intro i z P G t member entry shape
    exact ⟨(laws t).2 ⟨i,member,z,entry,P,G,t,shape,Or.inl rfl⟩,
      fun s lower => (laws s).2 ⟨i,member,z,entry,P,G,t,shape,Or.inr lower⟩⟩

theorem truth_mainLimitTopBirthFormula {n} (top cutoff birth : Fin n)
    (env : Fin n → ZFSet.{u}) : Truth (mainLimitTopBirthFormula top cutoff birth) env ↔
      ∀ x, ZFSet.pair x (env cutoff) ∈ env birth ↔ x = env top := by
  classical
  simp only [mainLimitTopBirthFormula, Truth, truth_pairMembershipFormula,
    truth_exGraphFields, not_exists, not_and, not_not]
  change (ZFSet.pair (env top) (env cutoff) ∈ env birth ∧
    ∀ x t, ZFSet.pair x t ∈ env birth → t = env cutoff → x = env top) ↔ _
  constructor
  · rintro ⟨entry,unique⟩ x
    exact ⟨fun image => unique x (env cutoff) image rfl, fun equal => equal.symm ▸ entry⟩
  · intro laws
    exact ⟨(laws (env top)).2 rfl, fun x t image equal => (laws x).1 (equal ▸ image)⟩

theorem truth_mainLimitCoverageFormula {n} (T S row Q H R top cutoff birth : Fin n)
    (env : Fin n → ZFSet.{u}) : Truth (mainLimitCoverageFormula T S row Q H R top cutoff birth) env ↔
      MainLimitCoverageGraphCode (env T) (env S) (env row) (env Q) (env H) (env R)
        (env top) (env cutoff) (env birth) := by
  simp only [mainLimitCoverageFormula, Truth, truth_mainLimitPointCoverageFormula,
    truth_mainLimitActorCoverageFormula, truth_mainLimitStrictTopFormula,
    truth_mainLimitCutoffFormula, truth_mainLimitTopBirthFormula]
  exact ⟨fun h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩,
    fun h => ⟨h.points,h.actors,h.strict_top,h.cutoff_mem,h.top_birth⟩⟩

end PartitionPilot.Forcing.BoundedFormula

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_MainPrefixValidityFormulas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula
universe u
namespace BoundedFormula

theorem truth_pairedTransitionEntryFormula {n} (i j p a E : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (pairedTransitionEntryFormula i j p a E) env ↔
      ZFSet.pair (ZFSet.pair (env j) (env i)) (ZFSet.pair (env p) (env a)) ∈ env E := by
  simp only [pairedTransitionEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_orderedTripleFormula]
  change (∃ w ∈ env E, ∃ b ∈ w, ∃ c ∈ b, c = ZFSet.pair (env p) (env a) ∧
    w = ZFSet.pair (ZFSet.pair (env j) (env i)) c) ↔ _
  constructor
  · rintro ⟨w, hw, b, _, c, _, rfl, rfl⟩
    exact hw
  · intro entry
    refine ⟨_, entry, {ZFSet.pair (env j) (env i), ZFSet.pair (env p) (env a)},
      ZFSet.mem_pair.2 (Or.inr rfl), _, ZFSet.mem_pair.2 (Or.inr rfl), rfl, rfl⟩

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_mainPrefixIdentityFormula {n} (E : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (mainPrefixIdentityFormula E) env ↔
      ∀ i p a, ZFSet.pair (ZFSet.pair i i) (ZFSet.pair p a) ∈ env E →
        GraphDiagonalCode p ∧ GraphDiagonalCode a := by
  rw [mainPrefixIdentityFormula, realize_allBlock]
  have actual (fields : Fin 3 → ZFSet.{u}) (ground : ∀ j, fields j ∈ M.sets) :=
    BoundedFormula.realize_toFormula M
      (BoundedFormula.imp
        (BoundedFormula.pairedTransitionEntryFormula (prefixIndex n 3 0) (prefixIndex n 3 0)
          (prefixIndex n 3 1) (prefixIndex n 3 2) (suffixIndex n 3 E))
        (.conj (BoundedFormula.graphDiagonalFormula (prefixIndex n 3 1))
          (BoundedFormula.graphDiagonalFormula (prefixIndex n 3 2))))
      (extendMany 3 fields env) (extendMany_members 3 fields env ground members)
  simp only [BoundedFormula.truth_imp, BoundedFormula.Truth,
    BoundedFormula.truth_pairedTransitionEntryFormula, BoundedFormula.truth_graphDiagonalFormula,
    extendMany_prefix, extendMany_suffix] at actual
  constructor
  · intro recognized i p a entry
    have hg := M.transitive (members E) entry
    let fields : Fin 3 → ZFSet.{u} := Fin.cases i (Fin.cases p (fun _ => a))
    have ground : ∀ j, fields j ∈ M.sets := Fin.cases (M.pair_left (M.pair_left hg))
      (Fin.cases (M.pair_left (M.pair_right hg)) (fun _ => M.pair_right (M.pair_right hg)))
    exact (actual fields ground).1 (recognized fields ground) entry
  · intro law fields ground
    exact (actual fields ground).2 (law (fields 0) (fields 1) (fields 2))

theorem realize_mainPrefixCompositionFormula {n} (E : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (mainPrefixCompositionFormula E) env ↔
      ∀ i j k p₁ a₁ p₂ a₂ p₃ a₃,
        ZFSet.pair (ZFSet.pair j i) (ZFSet.pair p₁ a₁) ∈ env E →
        ZFSet.pair (ZFSet.pair k j) (ZFSet.pair p₂ a₂) ∈ env E →
        ZFSet.pair (ZFSet.pair k i) (ZFSet.pair p₃ a₃) ∈ env E →
        GraphCompositionCode p₁ p₂ p₃ ∧ GraphCompositionCode a₁ a₂ a₃ := by
  rw [mainPrefixCompositionFormula, realize_allBlock]
  have actual (fields : Fin 9 → ZFSet.{u}) (ground : ∀ j, fields j ∈ M.sets) :=
    BoundedFormula.realize_toFormula M
      (BoundedFormula.imp
        (BoundedFormula.pairedTransitionEntryFormula (prefixIndex n 9 0) (prefixIndex n 9 1)
          (prefixIndex n 9 3) (prefixIndex n 9 4) (suffixIndex n 9 E))
        (BoundedFormula.imp
          (BoundedFormula.pairedTransitionEntryFormula (prefixIndex n 9 1) (prefixIndex n 9 2)
            (prefixIndex n 9 5) (prefixIndex n 9 6) (suffixIndex n 9 E))
          (BoundedFormula.imp
            (BoundedFormula.pairedTransitionEntryFormula (prefixIndex n 9 0) (prefixIndex n 9 2)
              (prefixIndex n 9 7) (prefixIndex n 9 8) (suffixIndex n 9 E))
            (.conj (BoundedFormula.graphCompositionFormula (prefixIndex n 9 3) (prefixIndex n 9 5) (prefixIndex n 9 7))
              (BoundedFormula.graphCompositionFormula (prefixIndex n 9 4) (prefixIndex n 9 6) (prefixIndex n 9 8))))))
      (extendMany 9 fields env) (extendMany_members 9 fields env ground members)
  simp only [BoundedFormula.truth_imp, BoundedFormula.Truth,
    BoundedFormula.truth_pairedTransitionEntryFormula, BoundedFormula.truth_graphCompositionFormula,
    extendMany_prefix, extendMany_suffix] at actual
  constructor
  · intro recognized i j k p₁ a₁ p₂ a₂ p₃ a₃ first second third
    have h₁ := M.transitive (members E) first
    have h₂ := M.transitive (members E) second
    have h₃ := M.transitive (members E) third
    let fields : Fin 9 → ZFSet.{u} := Fin.cases i (Fin.cases j (Fin.cases k (Fin.cases p₁
      (Fin.cases a₁ (Fin.cases p₂ (Fin.cases a₂ (Fin.cases p₃ (fun _ => a₃))))))))
    have ground : ∀ a, fields a ∈ M.sets := Fin.cases (M.pair_right (M.pair_left h₁))
      (Fin.cases (M.pair_left (M.pair_left h₁)) (Fin.cases (M.pair_left (M.pair_left h₂))
      (Fin.cases (M.pair_left (M.pair_right h₁)) (Fin.cases (M.pair_right (M.pair_right h₁))
      (Fin.cases (M.pair_left (M.pair_right h₂)) (Fin.cases (M.pair_right (M.pair_right h₂))
      (Fin.cases (M.pair_left (M.pair_right h₃)) (fun _ => M.pair_right (M.pair_right h₃)))))))))
    exact (actual fields ground).1 (recognized fields ground) first second third
  · intro law fields ground
    exact (actual fields ground).2 (law (fields 0) (fields 1) (fields 2) (fields 3)
      (fields 4) (fields 5) (fields 6) (fields 7) (fields 8))

end TransitiveGround

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
include pairing unions powers separation collection

theorem realize_mainPrefixStagesFormula {n} (K Labels C D rD N S : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (mainPrefixStagesFormula K Labels C D rD N S) env ↔
      ∀ i a, ZFSet.pair i a ∈ env S →
        ∃ linked : GroundLinkedMainStage M (env K) (env Labels) (env C) (env D) (env rD),
          linked.code = a := by
  rw [mainPrefixStagesFormula, realize_allBlock]
  have actual (fields : Fin 2 → ZFSet.{u}) (ground : ∀ j, fields j ∈ M.sets) :
      Realize M.sets
        (imp (BoundedFormula.pairMembershipFormula (prefixIndex n 2 0) (prefixIndex n 2 1)
          (suffixIndex n 2 S)).toFormula
          (linkedMainStageFormula (suffixIndex n 2 K) (suffixIndex n 2 Labels)
            (suffixIndex n 2 C) (suffixIndex n 2 D) (suffixIndex n 2 rD)
            (suffixIndex n 2 N) (prefixIndex n 2 1))) (extendMany 2 fields env) ↔
        ZFSet.pair (fields 0) (fields 1) ∈ env S →
          ∃ linked : GroundLinkedMainStage M (env K) (env Labels) (env C) (env D) (env rD),
            linked.code = fields 1 := by
    rw [realize_imp, BoundedFormula.realize_toFormula M _ _
      (extendMany_members 2 fields env ground members), BoundedFormula.truth_pairMembershipFormula,
      M.realize_linkedMainStageFormula pairing unions powers separation collection _ _ _ _ _ _ _ _
        (extendMany_members 2 fields env ground members)
        (by simpa only [extendMany_suffix] using omega)
        (by simpa only [extendMany_suffix] using ordinal)]
    simp only [extendMany_prefix, extendMany_suffix]
    rfl
  constructor
  · intro recognized i a entry
    have hg := M.transitive (members S) entry
    let fields : Fin 2 → ZFSet.{u} := Fin.cases i (fun _ => a)
    have ground : ∀ j, fields j ∈ M.sets := Fin.cases (M.pair_left hg) (fun _ => M.pair_right hg)
    exact (actual fields ground).1 (recognized fields ground) entry
  · intro law fields ground
    exact (actual fields ground).2 (law (fields 0) (fields 1))

theorem realize_mainPrefixTransitionsFormula {n} (K Labels C D rD N S E : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (mainPrefixTransitionsFormula K Labels C D rD N S E) env ↔
      ∀ i j a b z, ZFSet.pair i a ∈ env S → ZFSet.pair j b ∈ env S →
        ZFSet.pair (ZFSet.pair j i) z ∈ env E →
        LinkedMainTransitionCode M (env K) (env Labels) (env C) (env D) (env rD) a b z := by
  rw [mainPrefixTransitionsFormula, realize_allBlock]
  have actual (fields : Fin 5 → ZFSet.{u}) (ground : ∀ j, fields j ∈ M.sets) :
      Realize M.sets
        (imp (BoundedFormula.conj
          (BoundedFormula.pairMembershipFormula (prefixIndex n 5 0) (prefixIndex n 5 2) (suffixIndex n 5 S))
          (.conj (BoundedFormula.pairMembershipFormula (prefixIndex n 5 1) (prefixIndex n 5 3) (suffixIndex n 5 S))
            (BoundedFormula.tripleMembershipFormula (prefixIndex n 5 1) (prefixIndex n 5 0) (prefixIndex n 5 4)
              (suffixIndex n 5 E)))).toFormula
          (linkedMainTransitionFormula (suffixIndex n 5 K) (suffixIndex n 5 Labels) (suffixIndex n 5 C)
            (suffixIndex n 5 D) (suffixIndex n 5 rD) (suffixIndex n 5 N)
            (prefixIndex n 5 2) (prefixIndex n 5 3) (prefixIndex n 5 4))) (extendMany 5 fields env) ↔
        (ZFSet.pair (fields 0) (fields 2) ∈ env S ∧ ZFSet.pair (fields 1) (fields 3) ∈ env S ∧
          ZFSet.pair (ZFSet.pair (fields 1) (fields 0)) (fields 4) ∈ env E) →
        LinkedMainTransitionCode M (env K) (env Labels) (env C) (env D) (env rD)
          (fields 2) (fields 3) (fields 4) := by
    rw [realize_imp, BoundedFormula.realize_toFormula M _ _
      (extendMany_members 5 fields env ground members)]
    simp only [BoundedFormula.Truth, BoundedFormula.truth_pairMembershipFormula,
      BoundedFormula.truth_tripleMembershipFormula]
    rw [M.realize_linkedMainTransitionFormula pairing unions powers separation collection _ _ _ _ _ _ _ _ _ _
      (extendMany_members 5 fields env ground members)
      (by simpa only [extendMany_suffix] using omega)
      (by simpa only [extendMany_suffix] using ordinal)]
    simp only [extendMany_prefix, extendMany_suffix]
  constructor
  · intro recognized i j a b z first second third
    have h₁ := M.transitive (members S) first
    have h₂ := M.transitive (members S) second
    have h₃ := M.transitive (members E) third
    let fields : Fin 5 → ZFSet.{u} := Fin.cases i (Fin.cases j (Fin.cases a (Fin.cases b (fun _ => z))))
    have ground : ∀ k, fields k ∈ M.sets := Fin.cases (M.pair_left h₁)
      (Fin.cases (M.pair_left h₂) (Fin.cases (M.pair_right h₁)
        (Fin.cases (M.pair_right h₂) (fun _ => M.pair_right h₃))))
    exact (actual fields ground).1 (recognized fields ground) ⟨first, second, third⟩
  · intro law fields ground
    exact (actual fields ground).2 (fun entries =>
      law (fields 0) (fields 1) (fields 2) (fields 3) (fields 4) entries.1 entries.2.1 entries.2.2)

end TransitiveGround
end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_FixedTopProfilePreservation
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

theorem relationImage_retarget_eq {A Q V F e : ZFSet.{u}}
    (shape : e ⊆ ZFSet.prod A Q) (subset : Q ⊆ V) :
    relationImage F V e = relationImage F Q e := by
  apply ZFSet.ext
  intro x
  rw [mem_relationImage, mem_relationImage]
  constructor
  · rintro ⟨_, f, hf, entry⟩
    exact ⟨(ZFSet.pair_mem_prod.1 (shape entry)).2, f, hf, entry⟩
  · rintro ⟨hx, f, hf, entry⟩
    exact ⟨subset hx, f, hf, entry⟩

namespace CodedCapProfile
variable {P r μ c E K F : ZFSet.{u}}

theorem fixedTop (profile : CodedCapProfile P r μ c E K F) (meet : MeetOrderCode P r μ) :
    CodedCapProfile (fixedTopCarrier P) (fixedTopOrder P r) (fixedTopMeet P r) c E K F := by
  refine ⟨fixedTopCarrier_old profile.target_mem, fixedTopCarrier_old profile.separator_mem,
    fixedTopCarrier_old profile.cap_mem, fun _ hf => fixedTopCarrier_old (profile.filter_subset hf),
    profile.nonempty, ?_, fixedTopOrder_subset P r profile.target_below_cap,
    fun lower => profile.cap_not_below_target ((fixedTopOrder_old_iff profile.target_mem).1 lower),
    fun lower => profile.separator_not_below_cap ((fixedTopOrder_old_iff profile.cap_mem).1 lower)⟩
  intro x hx above
  rcases (mem_fixedTopCarrier P x).1 hx with equal | oldx
  · subst x
    have positive : ∃ f ∈ F, ZFSet.pair f P ∈ fixedTopOrder P r := by
      obtain ⟨f, hf⟩ := profile.nonempty
      exact ⟨f, hf, fixedTopOrder_greatest (fixedTopCarrier_old (profile.filter_subset hf))⟩
    exact ⟨fun _ => fixedTopOrder_greatest (fixedTopCarrier_old profile.cap_mem),
      fun negative => False.elim (negative positive)⟩
  · have old := profile.profile x oldx ((fixedTopOrder_old_iff oldx).1 above)
    have positive : (∃ f ∈ F, ZFSet.pair f x ∈ fixedTopOrder P r) ↔
        ∃ f ∈ F, ZFSet.pair f x ∈ r := by
      simp only [fixedTopOrder_old_iff oldx]
    exact ⟨fun hp => fixedTopOrder_subset P r (old.1 (positive.1 hp)),
      fun hn => fixedTopMeet_subset meet (old.2 (fun hp => hn (positive.2 hp)))⟩

end CodedCapProfile

namespace OldProfilePreservationCode
variable {P r μ Q R ν e Filters : ZFSet.{u}}

theorem fixedTop (preserved : OldProfilePreservationCode P r μ Q R ν e Filters)
    (target : MeetOrderCode Q R ν) (shape : e ⊆ ZFSet.prod P Q) :
    OldProfilePreservationCode P r μ (fixedTopCarrier Q) (fixedTopOrder Q R)
      (fixedTopMeet Q R) e Filters := by
  intro F hF c hc E hE K hK profile c' _ E' _ K' _ imageC imageE imageK
  have inherited := preserved F hF c hc E hE K hK profile
    c' (ZFSet.pair_mem_prod.1 (shape imageC)).2
    E' (ZFSet.pair_mem_prod.1 (shape imageE)).2
    K' (ZFSet.pair_mem_prod.1 (shape imageK)).2 imageC imageE imageK
  rw [relationImage_retarget_eq shape (fixedTopCarrier_subset Q)]
  exact inherited.fixedTop target

end OldProfilePreservationCode

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundLinkedProfileTransitionRecognition
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

theorem realize_linkedProfilePreservingTransitionFormula_raw {n} (K Labels C D rD N sourceCode targetCode z : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (linkedProfilePreservingTransitionFormula K Labels C D rD N sourceCode targetCode z) env ↔
      ∃ fields : Fin 53 → ZFSet.{u}, (∀ j, fields j ∈ M.sets) ∧
        LinkedProfilePreservingTransitionRawCode M (env K) (env Labels) (env C) (env D) (env rD) (env N)
          (env sourceCode) (env targetCode) (env z) (fields 48) (fields 49) (fields 50) (fields 51) (fields 52)
          (fun j => fields (j.castAdd 29)) (fun j => fields (Fin.natAdd 24 (j.castAdd 5))) := by
  rw [linkedProfilePreservingTransitionFormula, realize_exBlock]
  have actual (fields : Fin 53 → ZFSet.{u}) (ground : ∀ j, fields j ∈ M.sets) :=
    M.realize_linkedProfilePreservingTransitionRawFormula pairing unions powers separation collection
      (suffixIndex n 53 K) (suffixIndex n 53 Labels) (suffixIndex n 53 C) (suffixIndex n 53 D)
      (suffixIndex n 53 rD) (suffixIndex n 53 N) (suffixIndex n 53 sourceCode)
      (suffixIndex n 53 targetCode) (suffixIndex n 53 z)
      (prefixIndex n 53 48) (prefixIndex n 53 49) (prefixIndex n 53 50) (prefixIndex n 53 51) (prefixIndex n 53 52)
      (fun j => prefixIndex n 53 (j.castAdd 29)) (fun j => prefixIndex n 53 (Fin.natAdd 24 (j.castAdd 5)))
      (extendMany 53 fields env) (extendMany_members 53 fields env ground members)
      (by simpa only [extendMany_suffix] using omega)
      (by simpa only [extendMany_suffix] using ordinal)
  simp only [extendMany_prefix, extendMany_suffix] at actual
  constructor
  · rintro ⟨fields, ground, recognized⟩
    exact ⟨fields, ground, (actual fields ground).1 recognized⟩
  · rintro ⟨fields, ground, raw⟩
    exact ⟨fields, ground, (actual fields ground).2 raw⟩

theorem realize_linkedProfilePreservingTransitionFormula {n} (K Labels C D rD N sourceCode targetCode z : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (linkedProfilePreservingTransitionFormula K Labels C D rD N sourceCode targetCode z) env ↔
      LinkedProfilePreservingTransitionCode M (env K) (env Labels) (env C) (env D) (env rD)
        (env sourceCode) (env targetCode) (env z) := by
  rw [M.realize_linkedProfilePreservingTransitionFormula_raw pairing unions powers separation collection
    K Labels C D rD N sourceCode targetCode z env members omega ordinal]
  constructor
  · rintro ⟨fields, ground, raw⟩
    exact raw.exists_transition pairing unions powers separation
      (fun j => ground (j.castAdd 29)) (fun j => ground (Fin.natAdd 24 (j.castAdd 5)))
      (ground 48) (ground 49) (members C) (members D) (members rD) omega
  · rintro ⟨source, target, sourceEq, targetEq, transition, codeEq, coverage, preserved⟩
    let extra : Fin 5 → ZFSet.{u} := Fin.cases transition.map.points (Fin.cases transition.map.actors
      (Fin.cases source.main.birth (Fin.cases target.main.birth
        (fun _ => M.groundPower source.main.stage.carrier))))
    let fields : Fin 53 → ZFSet.{u} := Fin.addCases (m := 24) (n := 29) source.rawFields (Fin.addCases (m := 24) (n := 5) target.rawFields extra)
    have extraGround : ∀ j, extra j ∈ M.sets :=
      Fin.cases transition.map.points_ground (Fin.cases transition.map.actors_ground
        (Fin.cases source.main.birth_ground (Fin.cases target.main.birth_ground
          (fun _ => M.groundPower_mem powers source.main.stage.carrier_ground))))
    have grounded : ∀ j, fields j ∈ M.sets := by
      intro j
      refine Fin.addCases (m := 24) (n := 29) ?_ ?_ j
      · intro k
        simpa only [fields, Fin.addCases_left] using source.rawFields_ground pairing k
      · intro k
        refine Fin.addCases (m := 24) (n := 5) ?_ ?_ k
        · intro a
          simpa only [fields, Fin.addCases_right, Fin.addCases_left] using target.rawFields_ground pairing a
        · intro a
          simpa only [fields, Fin.addCases_right] using extraGround a
    refine ⟨fields, grounded, ?_⟩
    have smap : (fun j : Fin 24 => fields (j.castAdd 29)) = source.rawFields := by
      funext j
      simp only [fields, Fin.addCases_left]
    have tmap : (fun j : Fin 24 => fields (Fin.natAdd 24 (j.castAdd 5))) = target.rawFields := by
      funext j
      simp only [fields, Fin.addCases_right, Fin.addCases_left]
    rw [smap, tmap, omega]
    change LinkedProfilePreservingTransitionRawCode M (env K) (env Labels) (env C) (env D) (env rD) ZFSet.omega
      (env sourceCode) (env targetCode) (env z) transition.map.points transition.map.actors
      (source.main.birth) (target.main.birth)
      (M.groundPower source.main.stage.carrier) source.rawFields target.rawFields
    rw [← sourceEq, ← targetEq, ← codeEq]
    exact source.profileTransition_rawFields target transition coverage preserved

end TransitiveGround
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
open SetFormula
universe u v

namespace GroundMainPrefix
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem linked_profile_code (preserved : run.PreservesOldProfiles) {i j : I} (before : i ≤ j) :
    LinkedProfilePreservingTransitionCode M K Labels C D rD
      (run.linked i).code (run.linked j).code (run.diagram.transition before).map.code := by
  refine ⟨run.linked i, run.linked j, rfl, rfl, ?_⟩
  rw [run.linked_main i, run.linked_main j]
  exact ⟨run.diagram.transition before, rfl, run.coverage before, preserved i j before⟩

theorem profile_graph_code (preserved : run.PreservesOldProfiles) :
    MainPrefixProfileGraphCode M K Labels C D rD run.stageGraph run.transitionGraph := by
  intro i j a b z first second entry
  obtain ⟨s, rfl⟩ := ZFSet.mem_range.1 (run.stageGraph_function.pair_source first)
  obtain ⟨t, rfl⟩ := ZFSet.mem_range.1 (run.stageGraph_function.pair_source second)
  have order := ((pair_mem_chronologyPairs _ _ _).1
    (run.transitionGraph_function.pair_source entry)).2.2
  have before := (run.key_order s t).2 order
  rw [(run.stageGraph_entry s a).1 first, (run.stageGraph_entry t b).1 second,
    (run.transitionGraph_entry before z).1 entry]
  exact run.linked_profile_code preserved before

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

namespace GroundMainPrefix
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem preserved_code (preserved : run.PreservesOldProfiles) :
    PreservedMainPrefixCode M K Labels C D rD run.code :=
  ⟨run.indices, run.stageGraph, run.transitionGraph, rfl, run.graph_code, run.profile_graph_code preserved⟩

end GroundMainPrefix

end PartitionPilot.Forcing



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

theorem realize_mainPrefixProfileGraphFormula {n} (K Labels C D rD N S E : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (mainPrefixProfileGraphFormula K Labels C D rD N S E) env ↔
      MainPrefixProfileGraphCode M (env K) (env Labels) (env C) (env D) (env rD) (env S) (env E) := by
  rw [mainPrefixProfileGraphFormula, realize_allBlock]
  have actual (fields : Fin 5 → ZFSet.{u}) (ground : ∀ j, fields j ∈ M.sets) :
      Realize M.sets
        (imp (BoundedFormula.conj
          (BoundedFormula.pairMembershipFormula (prefixIndex n 5 0) (prefixIndex n 5 2) (suffixIndex n 5 S))
          (.conj (BoundedFormula.pairMembershipFormula (prefixIndex n 5 1) (prefixIndex n 5 3) (suffixIndex n 5 S))
            (BoundedFormula.tripleMembershipFormula (prefixIndex n 5 1) (prefixIndex n 5 0) (prefixIndex n 5 4)
              (suffixIndex n 5 E)))).toFormula
          (linkedProfilePreservingTransitionFormula (suffixIndex n 5 K) (suffixIndex n 5 Labels) (suffixIndex n 5 C)
            (suffixIndex n 5 D) (suffixIndex n 5 rD) (suffixIndex n 5 N)
            (prefixIndex n 5 2) (prefixIndex n 5 3) (prefixIndex n 5 4))) (extendMany 5 fields env) ↔
        (ZFSet.pair (fields 0) (fields 2) ∈ env S ∧ ZFSet.pair (fields 1) (fields 3) ∈ env S ∧
          ZFSet.pair (ZFSet.pair (fields 1) (fields 0)) (fields 4) ∈ env E) →
        LinkedProfilePreservingTransitionCode M (env K) (env Labels) (env C) (env D) (env rD)
          (fields 2) (fields 3) (fields 4) := by
    rw [realize_imp, BoundedFormula.realize_toFormula M _ _
      (extendMany_members 5 fields env ground members)]
    simp only [BoundedFormula.Truth, BoundedFormula.truth_pairMembershipFormula,
      BoundedFormula.truth_tripleMembershipFormula]
    rw [M.realize_linkedProfilePreservingTransitionFormula pairing unions powers separation collection _ _ _ _ _ _ _ _ _ _
      (extendMany_members 5 fields env ground members)
      (by simpa only [extendMany_suffix] using omega)
      (by simpa only [extendMany_suffix] using ordinal)]
    simp only [extendMany_prefix, extendMany_suffix]
  constructor
  · intro recognized i j a b z first second third
    have h₁ := M.transitive (members S) first
    have h₂ := M.transitive (members S) second
    have h₃ := M.transitive (members E) third
    let fields : Fin 5 → ZFSet.{u} := Fin.cases i (Fin.cases j (Fin.cases a (Fin.cases b (fun _ => z))))
    have ground : ∀ k, fields k ∈ M.sets := Fin.cases (M.pair_left h₁)
      (Fin.cases (M.pair_left h₂) (Fin.cases (M.pair_right h₁)
        (Fin.cases (M.pair_right h₂) (fun _ => M.pair_right h₃))))
    exact (actual fields ground).1 (recognized fields ground) ⟨first, second, third⟩
  · intro law fields ground
    exact (actual fields ground).2 (fun entries =>
      law (fields 0) (fields 1) (fields 2) (fields 3) (fields 4) entries.1 entries.2.1 entries.2.2)

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

theorem realize_mainPrefixGraphBodyFormula {n} (K Labels C D rD N T S E J : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K))
    (pairs : env J = chronologyPairs (env T)) :
    Realize M.sets (mainPrefixGraphBodyFormula K Labels C D rD N T S E J) env ↔
      MainPrefixGraphCode M (env K) (env Labels) (env C) (env D) (env rD) (env T) (env S) (env E) := by
  change (Realize M.sets (BoundedFormula.ordinalFormula T).toFormula env ∧
    Realize M.sets (functionGraphOnFormula T S) env ∧
    Realize M.sets (functionGraphOnFormula J E) env ∧
    Realize M.sets (mainPrefixStagesFormula K Labels C D rD N S) env ∧
    Realize M.sets (mainPrefixTransitionsFormula K Labels C D rD N S E) env ∧
    Realize M.sets (mainPrefixIdentityFormula E) env ∧
    Realize M.sets (mainPrefixCompositionFormula E) env) ↔ _
  rw [BoundedFormula.realize_ordinalFormula M T env members, ← ordinalSetProperty_iff,
    M.realize_functionGraphOnFormula unions T S env members,
    M.realize_functionGraphOnFormula unions J E env members,
    M.realize_mainPrefixStagesFormula pairing unions powers separation collection K Labels C D rD N S env members omega ordinal,
    M.realize_mainPrefixTransitionsFormula pairing unions powers separation collection K Labels C D rD N S E env members omega ordinal,
    M.realize_mainPrefixIdentityFormula E env members,
    M.realize_mainPrefixCompositionFormula E env members, pairs]
  constructor
  · rintro ⟨ord, stages, transitions, valid, maps, self, comp⟩
    exact ⟨ord, stages, transitions, valid, maps, self, comp⟩
  · intro code
    exact ⟨code.ordinal, code.stages, code.transitions, code.stage_valid,
      code.transition_valid, code.identity, code.composition⟩

theorem realize_mainPrefixGraphFormula {n} (K Labels C D rD N T S E : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (mainPrefixGraphFormula K Labels C D rD N T S E) env ↔
      MainPrefixGraphCode M (env K) (env Labels) (env C) (env D) (env rD) (env T) (env S) (env E) := by
  rw [mainPrefixGraphFormula, realize_ex]
  constructor
  · rintro ⟨J, hJ, equation, body⟩
    have pairs := (BoundedFormula.realize_chronologyPairsEquationFormula M 0 T.succ
      (extend J env) (Fin.cases hJ members)).1 equation
    exact (M.realize_mainPrefixGraphBodyFormula pairing unions powers separation collection
      K.succ Labels.succ C.succ D.succ rD.succ N.succ T.succ S.succ E.succ 0
      (extend J env) (Fin.cases hJ members) omega ordinal pairs).1 body
  · intro code
    have ground := M.chronologyPairs_mem pairing unions powers separation (members T)
    refine ⟨chronologyPairs (env T), ground, ?_, ?_⟩
    · exact (BoundedFormula.realize_chronologyPairsEquationFormula M 0 T.succ
        (extend (chronologyPairs (env T)) env) (Fin.cases ground members)).2 rfl
    · exact (M.realize_mainPrefixGraphBodyFormula pairing unions powers separation collection
        K.succ Labels.succ C.succ D.succ rD.succ N.succ T.succ S.succ E.succ 0
        (extend (chronologyPairs (env T)) env) (Fin.cases ground members) omega ordinal rfl).2 code

end TransitiveGround

end PartitionPilot.Forcing

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

theorem code_valid : MainPrefixCode M K Labels C D rD run.code :=
  ⟨run.indices, run.stageGraph, run.transitionGraph, rfl, run.graph_code⟩

end GroundMainPrefix

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem mem_mainPrefixCandidates (B K Labels C D rD z : ZFSet.{u}) :
    z ∈ M.mainPrefixCandidates B K Labels C D rD ↔
      z ∈ B ∧ MainPrefixCode M K Labels C D rD z := ZFSet.mem_sep

end TransitiveGround

namespace GroundMainCandidateLevel
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}
variable (level : GroundMainCandidateLevel M K)

theorem mem_validMainPrefixes {Labels C D rD z : ZFSet.{u}} :
    z ∈ level.validMainPrefixes Labels C D rD ↔
      z ∈ level.carrier ∧ MainPrefixCode M K Labels C D rD z :=
  M.mem_mainPrefixCandidates level.carrier K Labels C D rD z

theorem prefix_mem_validMainPrefixes
    {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
    {unions : Realize M.sets SetFormula.union Fin.elim0}
    {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
    {Labels C D rD : ZFSet.{u}} {I : Type v} [Small.{u} I] [Preorder I]
    (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)
    (rank : ZFSet.rank run.code < ZFSet.rank K) : run.code ∈ level.validMainPrefixes Labels C D rD :=
  level.mem_validMainPrefixes.2 ⟨(level.membership _).2 ⟨run.code_ground, rank⟩, run.code_valid⟩

end GroundMainCandidateLevel
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

theorem exists_rankedAppendTaskBearing (last : I) (greatest : ∀ i, i ≤ last)
    (oldRank : ZFSet.rank run.code < ZFSet.rank K) (limit : Order.IsSuccLimit (ZFSet.rank K))
    (level : GroundMainCandidateLevel M K) {targetCode z : ZFSet.{u}}
    (targetRank : ZFSet.rank targetCode < ZFSet.rank K)
    (code : TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega
      (run.linked last).code targetCode z) :
    ∃ target : GroundLinkedMainStage M K Labels C D rD,
      ∃ step : GroundChronologicalMainTransition (run.diagram.stage last) target.main,
        ∃ covered : step.CoversOldBirths,
          ∃ extended : GroundMainPrefix M K Labels C D rD pairing unions powers separation (WithTop I),
            extended = run.appendLast last greatest target step covered ∧
            target.code = targetCode ∧ step.map.code = z ∧ step.PreservesOldProfiles ∧
            extended.code ∈ M.sets ∧ ZFSet.rank extended.code < ZFSet.rank K ∧
            extended.code ∈ level.validMainPrefixes Labels C D rD ∧
            extended.indices = insert run.indices run.indices ∧
            (∀ i : I, extended.linked (i : WithTop I) = run.linked i) ∧
            extended.linked ⊤ = target ∧
            extended.stageGraph = insert (ZFSet.pair run.indices targetCode) run.stageGraph ∧
            graphRestriction run.indices extended.stageGraph = run.stageGraph ∧
            graphRestriction (chronologyPairs run.indices) extended.transitionGraph = run.transitionGraph ∧
            (∀ (i j : I) (before : i ≤ j),
              (extended.diagram.transition (WithTop.coe_le_coe.mpr before)).map.code =
                (run.diagram.transition before).map.code) ∧
            (extended.diagram.transition (show (last : WithTop I) ≤ ⊤ from le_top)).map.code = z ∧
            (extended.diagram.transition (show (last : WithTop I) ≤ ⊤ from le_top)).map.points = step.map.points ∧
            (extended.diagram.transition (show (last : WithTop I) ≤ ⊤ from le_top)).map.actors = step.map.actors ∧
            TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega
              (run.linked last).code (extended.linked ⊤).code
              (extended.diagram.transition (show (last : WithTop I) ≤ ⊤ from le_top)).map.code := by
  obtain ⟨target, targetEqual, transition, mapEqual, coverage, profiles⟩ :=
    code.exists_from_linked pairing unions powers separation
  let step : GroundChronologicalMainTransition (run.diagram.stage last) target.main :=
    transition.retargetEq (run.linked_main last) rfl
  have covered : step.CoversOldBirths :=
    (transition.retargetEq_coversOldBirths_iff (run.linked_main last) rfl).2 coverage
  have stepCode : step.map.code = z :=
    (transition.retargetEq_code (run.linked_main last) rfl).trans mapEqual
  have stepProfiles : step.PreservesOldProfiles :=
    (transition.retargetEq_preservesOldProfiles_iff (run.linked_main last) rfl).2 profiles
  let extended := run.appendLast last greatest target step covered
  have rank : ZFSet.rank extended.code < ZFSet.rank K :=
    run.appendLast_code_rank_lt last greatest target step covered limit oldRank
      (targetEqual.symm ▸ targetRank)
  have lastStep := run.appendLast_transition_last last greatest target step covered
  have lastCode :
      (extended.diagram.transition (show (last : WithTop I) ≤ ⊤ from le_top)).map.code = z := by
    rw [lastStep]
    exact stepCode
  refine ⟨target, step, covered, extended, rfl, targetEqual, stepCode, stepProfiles,
    extended.code_ground, rank, level.prefix_mem_validMainPrefixes extended rank,
    run.appendLast_indices last greatest target step covered,
    run.appendLast_linked_old last greatest target step covered,
    run.appendLast_linked_top last greatest target step covered, ?_,
    run.appendLast_stageGraph_restrict last greatest target step covered,
    run.appendLast_transitionGraph_restrict last greatest target step covered,
    (fun _ _ _ => rfl), lastCode, ?_, ?_, ?_⟩
  · rw [run.appendLast_stageGraph last greatest target step covered, targetEqual]
  · rw [lastStep]
  · rw [lastStep]
  · rw [run.appendLast_linked_top last greatest target step covered, targetEqual, lastCode]
    exact code

end PartitionPilot.Forcing.GroundMainPrefix

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_preservedMainPrefixFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) {n} (K Labels C D rD N z : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (preservedMainPrefixFormula K Labels C D rD N z) env ↔
      PreservedMainPrefixCode M (env K) (env Labels) (env C) (env D) (env rD) (env z) := by
  rw [preservedMainPrefixFormula, realize_exBlock]
  let old := suffixIndex n 3
  let field := prefixIndex n 3
  have actual (f : Fin 3 → ZFSet.{u}) (ground : ∀ j, f j ∈ M.sets) :
      (Realize M.sets (BoundedFormula.mainPrefixTupleFormula (old z) (field 0) (field 1) (field 2)).toFormula
          (extendMany 3 f env) ∧
        Realize M.sets (mainPrefixGraphFormula (old K) (old Labels) (old C) (old D) (old rD) (old N)
          (field 0) (field 1) (field 2)) (extendMany 3 f env) ∧
        Realize M.sets (mainPrefixProfileGraphFormula (old K) (old Labels) (old C) (old D)
          (old rD) (old N) (field 1) (field 2)) (extendMany 3 f env)) ↔
      env z = mainPrefixCode (f 0) (f 1) (f 2) ∧
        MainPrefixGraphCode M (env K) (env Labels) (env C) (env D) (env rD) (f 0) (f 1) (f 2) ∧
        MainPrefixProfileGraphCode M (env K) (env Labels) (env C) (env D) (env rD) (f 1) (f 2) := by
    have mems := extendMany_members 3 f env ground members
    have tuple := BoundedFormula.realize_mainPrefixTupleFormula M
      (old z) (field 0) (field 1) (field 2) (extendMany 3 f env) mems
    have code := M.realize_mainPrefixGraphFormula pairing unions powers separation collection
      (old K) (old Labels) (old C) (old D) (old rD) (old N) (field 0) (field 1) (field 2)
      (extendMany 3 f env) mems
      (by simpa only [old, extendMany_suffix] using omega)
      (by simpa only [old, extendMany_suffix] using ordinal)
    have profiles := M.realize_mainPrefixProfileGraphFormula pairing unions powers separation collection
      (old K) (old Labels) (old C) (old D) (old rD) (old N) (field 1) (field 2)
      (extendMany 3 f env) mems
      (by simpa only [old, extendMany_suffix] using omega)
      (by simpa only [old, extendMany_suffix] using ordinal)
    rw [tuple, code, profiles]
    simp only [old, field, extendMany_prefix, extendMany_suffix]
  constructor
  · rintro ⟨f, ground, recognized⟩
    exact ⟨f 0, f 1, f 2, (actual f ground).1 recognized⟩
  · rintro ⟨T, S, E, encoded, code, preserved⟩
    have ground := M.mainPrefixCode_fields_mem (encoded ▸ members z)
    let f : Fin 3 → ZFSet.{u} := Fin.cases T (Fin.cases S (fun _ => E))
    have fieldsGround : ∀ j, f j ∈ M.sets := Fin.cases ground.1 (Fin.cases ground.2.1 (fun _ => ground.2.2))
    exact ⟨f, fieldsGround, (actual f fieldsGround).2 ⟨encoded, code, preserved⟩⟩

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixTopColumns
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

theorem heightRangeFamily_ground : run.heightRangeFamily ∈ M.sets :=
  M.familyCodeGraph_functionRanges_ground pairing unions powers separation run.key
    (fun i => (run.diagram.stage i).stage.carrier) (fun i => (run.diagram.stage i).stage.height)
    run.key_injective run.indices_ground run.carrierFamily_ground (run.stageFieldFamily_ground 10)

theorem heightRangeFamily_function : FunctionGraphOn run.indices run.heightRangeFamily :=
  familyCodeGraph_function run.key _ run.key_injective

theorem heightRange_stage_eq (i : I) :
    functionGraphRange (run.diagram.stage i).stage.carrier (run.diagram.stage i).stage.height =
      relationImage (run.diagram.stage i).stage.carrier (ZFSet.prod C D) (run.diagram.stage i).stage.height := by
  apply ZFSet.ext
  intro y
  rw [mem_functionGraphRange, mem_relationImage]
  constructor
  · intro h
    obtain ⟨x, hx, entry⟩ := h
    exact ⟨(ZFSet.pair_mem_prod.1 ((run.diagram.stage i).stage.height_code.function.1 entry)).2, x, hx, entry⟩
  · exact And.right

theorem heightRangeValues_ground : run.heightRangeValues ∈ M.sets :=
  M.familyCodeGraph_valueRange_mem unions separation run.key _ run.indices_ground run.heightRangeFamily_ground

theorem heightRangeValues_union : ⋃₀ run.heightRangeValues = run.limitHeightRange := by
  apply ZFSet.ext
  intro t
  rw [heightRangeValues, familyCodeGraph_valueUnion_mem_iff, run.limitHeightRange_mem]
  simp only [mem_functionGraphRange]

variable (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (indices : M.groundEmbeddable run.indices ZFSet.omega)
include infinite choice indices

theorem heightRangeValues_countable : M.groundEmbeddable run.heightRangeValues ZFSet.omega := by
  rw [heightRangeValues, familyCodeGraph_valueRange_eq run.key _]
  exact M.groundEmbeddable_function_image pairing unions powers separation choice
    run.indices_ground (M.union_mem unions (M.union_mem unions run.heightRangeFamily_ground))
    (M.omega_mem separation infinite) run.heightRangeFamily_ground
    run.heightRangeFamily_function.to_isFunc indices

theorem limitHeightRange_countable : M.groundEmbeddable run.limitHeightRange ZFSet.omega := by
  rw [← run.heightRangeValues_union]
  apply M.groundCountable_family_union pairing unions powers separation infinite choice
    run.heightRangeValues_ground (run.heightRangeValues_countable infinite choice indices)
  intro R hR
  obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hR
  change M.groundEmbeddable
    (functionGraphRange (run.diagram.stage i).stage.carrier (run.diagram.stage i).stage.height) ZFSet.omega
  rw [run.heightRange_stage_eq i]
  exact (run.diagram.stage i).stage.height_range_countable

end PartitionPilot.Forcing.GroundMainPrefix

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem limitHeight_relationImage_eq :
    relationImage run.limitPoints (ZFSet.prod C D) run.limitHeight = run.limitHeightRange := by
  apply ZFSet.ext
  intro y
  rw [limitHeightRange, mem_functionGraphRange, mem_relationImage]
  exact ⟨And.right, fun h =>
    ⟨(ZFSet.pair_mem_prod.1 (run.limitHeight_function.1 h.choose_spec.2)).2, h⟩⟩

theorem limitHeight_relationImage_countable
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (indices : M.groundEmbeddable run.indices ZFSet.omega) :
    M.groundEmbeddable (relationImage run.limitPoints (ZFSet.prod C D) run.limitHeight) ZFSet.omega := by
  rw [run.limitHeight_relationImage_eq]
  exact run.limitHeightRange_countable infinite choice indices

end PartitionPilot.Forcing.GroundMainPrefix

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

theorem exists_fixedTopMainStage (i₀ : I)
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (columns_eq : C = M.groundOmegaOne pairing unions powers separation collection infinite)
    (indices : M.groundEmbeddable run.indices ZFSet.omega) :
    Nonempty (run.FixedTopStage i₀) := by
  subst C
  have nonempty : D.Nonempty := by
    obtain ⟨value, entry, _⟩ := (run.diagram.stage i₀).stage.height_code.function.2
      (run.diagram.stage i₀).stage.bottom (run.diagram.stage i₀).stage.bottom_mem
    have member := (ZFSet.pair_mem_prod.1 ((run.diagram.stage i₀).stage.height_code.function.1 entry)).2
    obtain ⟨_, _, q, hq, _⟩ := ZFSet.mem_prod.1 member
    exact ⟨q, hq⟩
  obtain ⟨b, hb, q, hq, hL, hR, hMu, _, hAction, hHeight, meet, _, action, height,
      _, _, _, _, _, _, _, above, _, _, hRange, smallRange, _, _⟩ :=
    M.exists_fixedTopExtension pairing unions powers separation collection infinite choice
      run.limitPoints_ground run.limitOrder_ground run.limitActors_ground run.limitAction_ground
      (run.diagram.stage i₀).stage.coordinates_ground run.limitHeight_ground
      run.limitMeet_code (run.limitAction_code i₀) (run.limitIdentity_mem i₀) nonempty
      run.limitHeight_code (run.limitHeight_relationImage_countable infinite choice indices)
  let stage : GroundMainStage M (M.groundOmegaOne pairing unions powers separation collection infinite) D rD := {
    carrier := fixedTopCarrier run.limitPoints
    order := fixedTopOrder run.limitPoints run.limitOrder
    meetGraph := fixedTopMeet run.limitPoints run.limitOrder
    actors := run.limitActors
    multiplication := run.limitMultiplication
    inverse := run.limitInverse
    identity := run.limitIdentity i₀
    action := fixedTopAction run.limitActors run.limitPoints run.limitAction
    bottom := run.limitBottom i₀
    top := run.limitPoints
    height := fixedTopHeightGraph run.limitPoints run.limitHeight b q
    carrier_ground := hL
    order_ground := hR
    meet_ground := hMu
    actors_ground := run.limitActors_ground
    multiplication_ground := run.limitMultiplication_ground
    inverse_ground := run.limitInverse_ground
    action_ground := hAction
    height_ground := hHeight
    columns_ground := (run.diagram.stage i₀).stage.columns_ground
    coordinates_ground := (run.diagram.stage i₀).stage.coordinates_ground
    coordinate_order_ground := (run.diagram.stage i₀).stage.coordinate_order_ground
    meet := meet
    group_code := run.limitGroup_code i₀
    action_code := action
    bottom_mem := fixedTopCarrier_old (run.limitBottom_mem i₀)
    least := fixedTopOrder_bottom (run.limitBottom_mem i₀) (run.limitBottom_least i₀)
    top_mem := fixedTopCarrier_top run.limitPoints
    greatest := fun _ hx => fixedTopOrder_greatest hx
    height_code := height
    height_range_ground := hRange
    height_range_countable := smallRange }
  exact ⟨{
    column := b
    coordinate := q
    column_mem := hb
    coordinate_mem := hq
    stage := stage
    carrier_eq := rfl
    order_eq := rfl
    meet_eq := rfl
    actors_eq := rfl
    multiplication_eq := rfl
    inverse_eq := rfl
    identity_eq := rfl
    action_eq := rfl
    bottom_eq := rfl
    top_eq := rfl
    height_eq := rfl
    column_above := above }⟩

end GroundMainPrefix

namespace GroundMainPrefix.FixedTopStage
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {i₀ : I} (data : run.FixedTopStage i₀)

theorem height_rank_lt (infinite : Realize M.sets infinity Fin.elim0)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (rank : ZFSet.rank run.code < ZFSet.rank K) : ZFSet.rank data.stage.height < ZFSet.rank K := by
  have conditions := standard.to_conditions pairing unions powers separation hK
  have limit := conditions.rank_isLimit pairing unions powers separation infinite hK
  exact rank_functionGraph_lt limit data.stage.height_code.function (data.carrier_rank_lt limit rank)
    (rank_product_lt limit (run.linked i₀).invariant.columns_rank (run.linked i₀).invariant.coordinates_rank)

end GroundMainPrefix.FixedTopStage

namespace GroundMainPrefix.FixedTopStage
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {i₀ : I} (data : run.FixedTopStage i₀)

theorem transition_points (i : I) : (data.transition i).points = run.limitPointMap i := rfl

theorem point_strict_top (i : I) {x y : ZFSet.{u}}
    (entry : ZFSet.pair x y ∈ run.limitPointMap i) :
    ZFSet.pair y data.stage.top ∈ data.stage.order ∧
      ZFSet.pair data.stage.top y ∉ data.stage.order := by
  rw [data.top_eq, data.order_eq]
  exact fixedTopOrder_strict_top run.limitOrder_code
    (ZFSet.pair_mem_prod.1 ((run.limitPointMap_injection i).function.1 entry)).2

end GroundMainPrefix.FixedTopStage

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

namespace GroundMainPrefix.FixedTopStage
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {i₀ : I} (data : run.FixedTopStage i₀)

theorem exists_rankedChronology
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (indices : GroundBelow M run.indices K) (rank : ZFSet.rank run.code < ZFSet.rank K)
    (level : GroundMainCandidateLevel M K) : Nonempty (data.RankedChronology level) := by
  obtain ⟨prior, _, priorRank, _, priorGraphs, priorValues, _⟩ :=
    run.exists_limitSerialization collection infinite choice hK standard indices rank level
  have terminal (j : Fin 5) : prior.fields.value j run.cutoffLimit = run.limitTerminalFields j :=
    (priorValues j run.cutoffLimit).trans (run.limitChronologyFields_terminal j)
  have newValues : prior.fixedTopValues data.stage.height = data.chronologyValues := by
    funext j
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun _ => rfl)))) j
    · change fixedTopCarrier (prior.fields.value 0 run.cutoffLimit) = data.stage.carrier
      rw [terminal 0]
      exact data.carrier_eq.symm
    · change fixedTopOrder (prior.fields.value 0 run.cutoffLimit)
        (prior.fields.value 1 run.cutoffLimit) = data.stage.order
      rw [terminal 0, terminal 1]
      exact data.order_eq.symm
    · change fixedTopMeet (prior.fields.value 0 run.cutoffLimit)
        (prior.fields.value 1 run.cutoffLimit) = data.stage.meetGraph
      rw [terminal 0, terminal 1]
      exact data.meet_eq.symm
    · change fixedTopBirth (prior.fields.value 0 run.cutoffLimit)
        (prior.fields.value 3 run.cutoffLimit) run.cutoffLimit = _
      rw [terminal 0, terminal 3]
      rfl
  have conditions := standard.to_conditions pairing unions powers separation hK
  have earlier : ∀ x t, ZFSet.pair x t ∈ prior.fields.value 3 run.cutoffLimit → t ∈ run.cutoffLimit := by
    intro x t entry
    rw [terminal 3] at entry
    exact (ZFSet.pair_mem_prod.1 (run.limitBirth_function.1 entry)).2
  have height : StrictLexHeightCode (fixedTopCarrier (prior.fields.value 0 run.cutoffLimit)) C D
      (fixedTopOrder (prior.fields.value 0 run.cutoffLimit) (prior.fields.value 1 run.cutoffLimit))
      data.stage.height rD := by
    rw [terminal 0, terminal 1]
    change StrictLexHeightCode (fixedTopCarrier run.limitPoints) C D
      (fixedTopOrder run.limitPoints run.limitOrder) data.stage.height rD
    rw [← data.carrier_eq, ← data.order_eq]
    exact data.stage.height_code
  obtain ⟨extended, ground, extendedRank, member, graphs, values⟩ :=
    prior.exists_rankedFixedTopSerialization pairing unions powers separation collection infinite choice
      hK conditions (conditions.successor_mem pairing unions powers separation infinite hK
        (run.cutoffLimit_mem_inaccessible hK standard indices)) level priorRank
      data.stage.height data.stage.height_ground (data.height_rank_lt infinite hK standard rank)
      run.cutoffLimit_ordinal earlier height
  refine ⟨⟨extended, ground, extendedRank, member, ?_, ?_, ?_⟩⟩
  · intro j
    rw [congrFun graphs j]
    change terminalChronologyGraph run.cutoffLimit (prior.fields.graph j)
      (prior.fixedTopValues data.stage.height j) = _
    rw [priorGraphs, newValues]
  · intro j
    rw [values j run.cutoffLimit (ZFSet.mem_insert _ _), appendHistoryValue_at, newValues]
  · intro j s hs
    rw [values j s (ZFSet.mem_insert_of_mem _ hs), appendHistoryValue_old hs, priorValues]

end GroundMainPrefix.FixedTopStage

namespace GroundMainPrefix.FixedTopStage.RankedChronology
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {i₀ : I} {data : run.FixedTopStage i₀} {level : GroundMainCandidateLevel M K}
variable (chronology : data.RankedChronology level)

theorem coversOldBirths (i : I) : (chronology.transition i).CoversOldBirths := by
  intro y t entry before
  rw [chronology.main_birth] at entry
  have strict : t ∈ run.cutoffLimit := (run.cutoffLimit_mem t).2 ⟨i, before⟩
  have old := (fixedTopBirth_earlier_iff strict).1 entry
  obtain ⟨x, hx, _, image⟩ := (run.limitBirth_old_fiber i y t before).1 old
  exact ⟨x, hx, image⟩

end GroundMainPrefix.FixedTopStage.RankedChronology

namespace GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}

namespace FixedTopStage.RankedChronology
variable {i₀ : I} {data : run.FixedTopStage i₀} {level : GroundMainCandidateLevel M K}
variable (chronology : data.RankedChronology level)

theorem cone_coverage : chronology.cone.append.CoversOldBirths :=
  chronology.cone.append_coverage run.coverage chronology.coversOldBirths

end FixedTopStage.RankedChronology

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

theorem limitPointMap_coverage_iff (x : ZFSet.{u}) :
    x ∈ run.limitPoints ↔ ∃ i y, y ∈ (run.diagram.stage i).stage.carrier ∧
      ZFSet.pair y x ∈ run.limitPointMap i := by
  constructor
  · intro member
    obtain ⟨i, y, hy, equal⟩ := run.pointPresentation.limitPoint_coverage member
    exact ⟨i, y, hy, (run.pointPresentation.inclusion_entry i y x).2 ⟨hy, equal⟩⟩
  · rintro ⟨i, y, _, entry⟩
    exact (ZFSet.pair_mem_prod.1 ((run.limitPointMap_injection i).function.1 entry)).2

theorem limitActorMap_coverage_iff (g : ZFSet.{u}) :
    g ∈ run.limitActors ↔ ∃ i h, h ∈ (run.diagram.stage i).stage.actors ∧
      ZFSet.pair h g ∈ run.limitActorMap i := by
  constructor
  · intro member
    obtain ⟨i, h, hh, equal⟩ := run.actorPresentation.limitPoint_coverage member
    exact ⟨i, h, hh, (run.actorPresentation.inclusion_entry i h g).2 ⟨hh, equal⟩⟩
  · rintro ⟨i, h, _, entry⟩
    exact (ZFSet.pair_mem_prod.1 ((run.limitActorMap_injection i).function.1 entry)).2

namespace FixedTopStage.RankedChronology
variable {run} {i₀ : I} {data : run.FixedTopStage i₀} {level : GroundMainCandidateLevel M K}
variable (chronology : data.RankedChronology level)

theorem limitCoverage : run.LimitCoverage chronology.main chronology.cone := by
  refine ⟨?_, ?_, ?_, rfl, ?_⟩
  · intro x
    change (x ∈ data.stage.carrier ∧ x ≠ data.stage.top) ↔
      ∃ i y, y ∈ (run.diagram.stage i).stage.carrier ∧ ZFSet.pair y x ∈ run.limitPointMap i
    rw [data.carrier_eq, data.top_eq, ← run.limitPointMap_coverage_iff]
    constructor
    · rintro ⟨member, different⟩
      exact ((mem_fixedTopCarrier run.limitPoints x).1 member).resolve_left different
    · intro member
      exact ⟨fixedTopCarrier_old member, fun equal => ZFSet.mem_irrefl _ (equal ▸ member)⟩
  · intro g
    change g ∈ data.stage.actors ↔
      ∃ i h, h ∈ (run.diagram.stage i).stage.actors ∧ ZFSet.pair h g ∈ run.limitActorMap i
    rw [data.actors_eq]
    exact run.limitActorMap_coverage_iff g
  · intro i x y entry
    exact data.point_strict_top i entry
  · intro x
    rw [chronology.main_birth]
    change ZFSet.pair x run.cutoffLimit ∈ fixedTopBirth run.limitPoints run.limitBirth run.cutoffLimit ↔
      x = data.stage.top
    rw [data.top_eq]
    exact fixedTopBirth_new_time_iff (fun _ _ entry =>
      (ZFSet.pair_mem_prod.1 (run.limitBirth_function.1 entry)).2)

end FixedTopStage.RankedChronology
end GroundMainPrefix

end PartitionPilot.Forcing

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

theorem limitPointMap_oldProfilePreservation (preserved : run.PreservesOldProfiles) (i : I) :
    OldProfilePreservationCode (run.diagram.stage i).stage.carrier
      (run.diagram.stage i).stage.order (run.diagram.stage i).stage.meetGraph
      run.limitPoints run.limitOrder run.limitMeetGraph (run.limitPointMap i)
      (M.groundPower (run.diagram.stage i).stage.carrier) := by
  intro F hF c hc E hE cap hcap profile c' hc' E' hE' cap' hcap' imageC imageE imageCap
  let embedding := run.limitPointMap_meetEmbedding i
  refine ⟨hc', hE', hcap', fun _ member => ((mem_relationImage _ _ _ _).1 member).1,
    ?_, ?_, embedding.monotone c cap c' cap' profile.target_below_cap imageC imageCap,
    fun lower => profile.cap_not_below_target
      ((run.limitPointMap_order_iff i cap c cap' c' imageCap imageC).1 lower),
    fun lower => profile.separator_not_below_cap
      ((run.limitPointMap_order_iff i E cap E' cap' imageE imageCap).1 lower)⟩
  · obtain ⟨f, hf⟩ := profile.nonempty
    obtain ⟨f', entry, _⟩ := embedding.injection.function.2 f (profile.filter_subset hf)
    exact ⟨f', (mem_relationImage _ _ _ _).2
      ⟨(ZFSet.pair_mem_prod.1 (embedding.injection.function.1 entry)).2, f, hf, entry⟩⟩
  · intro q hq above
    obtain ⟨j, x, hx, equal⟩ := run.pointPresentation.limitPoint_coverage hq
    have imageX : ZFSet.pair x q ∈ run.limitPointMap j :=
      (run.pointPresentation.inclusion_entry j x q).2 ⟨hx, equal⟩
    obtain ⟨k, ik, jk⟩ := run.common_upper i j
    obtain ⟨cK, cEntry⟩ := run.pointSystem.map_entry_total ik hc
    obtain ⟨eK, eEntry⟩ := run.pointSystem.map_entry_total ik hE
    obtain ⟨capK, capEntry⟩ := run.pointSystem.map_entry_total ik hcap
    obtain ⟨xK, xEntry⟩ := run.pointSystem.map_entry_total jk hx
    have atStage := preserved i k ik F hF c hc E hE cap hcap profile
      cK (run.pointSystem.map_entry_bounds ik cEntry).2
      eK (run.pointSystem.map_entry_bounds ik eEntry).2
      capK (run.pointSystem.map_entry_bounds ik capEntry).2 cEntry eEntry capEntry
    have tested := atStage.profile.at_embedding (run.limitPointMap_meetEmbedding k)
      (run.diagram.stage k).stage.meet run.limitMeet_code atStage.filter_subset
      (run.limitPointMap_later_entry ik cEntry imageC)
      (run.limitPointMap_later_entry ik eEntry imageE)
      (run.limitPointMap_later_entry ik capEntry imageCap)
      (run.limitPointMap_later_entry jk xEntry imageX) above
    have imageEqual :
        relationImage (relationImage F (run.diagram.stage k).stage.carrier
          (run.diagram.transition ik).map.points) run.limitPoints (run.limitPointMap k) =
        relationImage F run.limitPoints (run.limitPointMap i) :=
      (relationImage_composition_on profile.filter_subset).trans
        (congrArg (relationImage F run.limitPoints) (run.limitPointMap_comp ik))
    rw [imageEqual] at tested
    exact tested

end GroundMainPrefix

section
open SetFormula SetRealization
universe u v

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem mem_preservedMainPrefixCandidates (B K Labels C D rD z : ZFSet.{u}) :
    z ∈ M.preservedMainPrefixCandidates B K Labels C D rD ↔
      z ∈ B ∧ PreservedMainPrefixCode M K Labels C D rD z := ZFSet.mem_sep

theorem preservedMainPrefixCandidates_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    {B K Labels C D rD : ZFSet.{u}} (hB : B ∈ M.sets) (hK : K ∈ M.sets)
    (hLabels : Labels ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (ordinal : ordinalSetProperty K) : M.preservedMainPrefixCandidates B K Labels C D rD ∈ M.sets := by
  let params := extend K (extend Labels (extend C (extend D (extend rD (extend ZFSet.omega Fin.elim0)))))
  have ground : ∀ j, params j ∈ M.sets := Fin.cases hK (Fin.cases hLabels (Fin.cases hC
    (Fin.cases hD (Fin.cases hrD (Fin.cases (M.omega_mem separation infinite) (fun i => Fin.elim0 i))))))
  have selected := M.separation_mem separation (preservedMainPrefixFormula 1 2 3 4 5 6 0) params ground hB
  have equal : ZFSet.sep (fun z => Realize M.sets (preservedMainPrefixFormula 1 2 3 4 5 6 0)
      (extend z params)) B = M.preservedMainPrefixCandidates B K Labels C D rD := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, M.mem_preservedMainPrefixCandidates]
    apply and_congr_right
    intro hz
    exact M.realize_preservedMainPrefixFormula pairing unions powers separation collection 1 2 3 4 5 6 0
      (extend z params) (Fin.cases (M.transitive hB hz) ground) rfl ordinal
  exact equal ▸ selected

end TransitiveGround

namespace GroundMainCandidateLevel
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}
variable (level : GroundMainCandidateLevel M K)

theorem preservedMainPrefixes_ground
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (hK : K ∈ M.sets) (ordinal : ordinalSetProperty K) {Labels C D rD : ZFSet.{u}}
    (hLabels : Labels ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) :
    level.preservedMainPrefixes Labels C D rD ∈ M.sets :=
  M.preservedMainPrefixCandidates_mem pairing unions powers separation collection infinite
    level.carrier_ground hK hLabels hC hD hrD ordinal

theorem mem_preservedMainPrefixes {Labels C D rD z : ZFSet.{u}} :
    z ∈ level.preservedMainPrefixes Labels C D rD ↔
      z ∈ level.carrier ∧ PreservedMainPrefixCode M K Labels C D rD z :=
  M.mem_preservedMainPrefixCandidates level.carrier K Labels C D rD z

theorem prefix_mem_preservedMainPrefixes
    {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
    {unions : Realize M.sets SetFormula.union Fin.elim0}
    {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
    {Labels C D rD : ZFSet.{u}} {I : Type v} [Small.{u} I] [Preorder I]
    (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)
    (preserved : run.PreservesOldProfiles)
    (rank : ZFSet.rank run.code < ZFSet.rank K) : run.code ∈ level.preservedMainPrefixes Labels C D rD :=
  level.mem_preservedMainPrefixes.2 ⟨(level.membership _).2 ⟨run.code_ground, rank⟩, run.preserved_code preserved⟩

theorem exists_preservedPrefix_of_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {Labels C D rD z : ZFSet.{u}}
    (member : z ∈ level.preservedMainPrefixes Labels C D rD) :
    ∃ T ∈ M.sets, ∃ ordinal : ordinalSetProperty T,
      letI := ordinalMainIndexPreorder ordinal
      ∃ run : GroundMainPrefix M K Labels C D rD pairing unions powers separation (SetMembers T),
        run.indices = T ∧ run.code = z ∧ run.PreservesOldProfiles ∧ ZFSet.rank run.code < ZFSet.rank K := by
  obtain ⟨carrier, code⟩ := level.mem_preservedMainPrefixes.1 member
  obtain ⟨ground, rank⟩ := (level.membership z).1 carrier
  obtain ⟨T, hT, ordinal, run, indices, equal, preserved⟩ :=
    code.exists_decodedPrefix pairing unions powers separation ground
  exact ⟨T, hT, ordinal, run, indices, equal, preserved, equal.symm ▸ rank⟩

end GroundMainCandidateLevel
end

namespace GroundMainPrefix.FixedTopStage
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {i₀ : I} (data : run.FixedTopStage i₀)

theorem transition_oldProfilePreservation (preserved : run.PreservesOldProfiles) (i : I) :
    OldProfilePreservationCode (run.diagram.stage i).stage.carrier
      (run.diagram.stage i).stage.order (run.diagram.stage i).stage.meetGraph
      data.stage.carrier data.stage.order data.stage.meetGraph (data.transition i).points
      (M.groundPower (run.diagram.stage i).stage.carrier) := by
  rw [data.carrier_eq, data.order_eq, data.meet_eq, data.transition_points]
  exact (run.limitPointMap_oldProfilePreservation preserved i).fixedTop run.limitMeet_code
    (run.limitPointMap_injection i).function.1

namespace RankedChronology
variable {data} {level : GroundMainCandidateLevel M K} (chronology : data.RankedChronology level)

theorem transition_preservesOldProfiles (preserved : run.PreservesOldProfiles) (i : I) :
    (chronology.transition i).PreservesOldProfiles :=
  data.transition_oldProfilePreservation preserved i

end RankedChronology
end GroundMainPrefix.FixedTopStage

namespace GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem exists_rawCoveredPreservedAppendLimit (preserved : run.PreservesOldProfiles) (i₀ : I)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (columns_eq : C = M.groundOmegaOne pairing unions powers separation collection infinite)
    (indexMember : run.indices ∈ M.groundOmegaOne pairing unions powers separation collection infinite)
    (oldRank : ZFSet.rank run.code < ZFSet.rank K)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (level : GroundMainCandidateLevel M K) :
    ∃ data : run.FixedTopStage i₀,
      ∃ chronology : data.RankedChronology level,
      ∃ target : GroundLinkedMainStage M K Labels C D rD,
        ∃ extended : GroundMainPrefix M K Labels C D rD pairing unions powers separation (WithTop I),
          (∀ i : I, extended.key (i : WithTop I) = run.key i) ∧
          extended.key ⊤ = run.indices ∧
          (∀ i z, ZFSet.pair (ZFSet.pair run.indices (run.key i)) z ∈ extended.transitionGraph ↔
            z = (chronology.cone.leg i).map.code) ∧
          run.LimitCoverage chronology.main chronology.cone ∧
          MainLimitCoverageGraphCode run.indices run.stageGraph extended.transitionGraph
            target.main.stage.carrier target.main.stage.actors target.main.stage.order
            target.main.stage.top target.main.cutoff target.main.birth ∧
          target.main = chronology.main ∧
          target.serial.code = chronology.serial.code ∧
          extended.PreservesOldProfiles ∧
          target.main.stage = data.stage ∧ target.main.cutoff = run.cutoffLimit ∧
          target.main.birth = fixedTopBirth run.limitPoints run.limitBirth run.cutoffLimit ∧
          target.serial.code ∈ level.validChronologies C D rD ∧
          extended.indices = insert run.indices run.indices ∧
          extended.indices ∈ M.groundOmegaOne pairing unions powers separation collection infinite ∧
          extended.code ∈ M.sets ∧ ZFSet.rank extended.code < ZFSet.rank K ∧
          extended.code ∈ level.validMainPrefixes Labels C D rD ∧
          extended.code ∈ level.preservedMainPrefixes Labels C D rD ∧
          (∀ i : I, extended.linked (i : WithTop I) = run.linked i) ∧
          extended.linked ⊤ = target ∧
          extended.stageGraph = insert (ZFSet.pair run.indices target.code) run.stageGraph ∧
          graphRestriction run.indices extended.stageGraph = run.stageGraph ∧
          graphRestriction (chronologyPairs run.indices) extended.transitionGraph = run.transitionGraph ∧
          (∀ (i j : I) (before : i ≤ j),
            (extended.diagram.transition (WithTop.coe_le_coe.mpr before)).map.code =
              (run.diagram.transition before).map.code) ∧
          (∀ i : I,
            (extended.diagram.transition (show (i : WithTop I) ≤ ⊤ from le_top)).map.points = run.limitPointMap i ∧
            (extended.diagram.transition (show (i : WithTop I) ≤ ⊤ from le_top)).map.actors = run.limitActorMap i) ∧
          (∀ (i : I) (x y : ZFSet.{u}), ZFSet.pair x y ∈ run.limitPointMap i →
            ZFSet.pair y target.main.stage.top ∈ target.main.stage.order ∧
              ZFSet.pair target.main.stage.top y ∉ target.main.stage.order) := by
  have indices := M.groundOmegaOne_member_countable pairing unions powers separation collection infinite indexMember
  have below : GroundBelow M run.indices K :=
    ⟨ZFSet.omega, standard.omega_mem pairing unions powers separation hK, indices⟩
  obtain ⟨data⟩ := run.exists_fixedTopMainStage i₀ collection infinite choice columns_eq indices
  obtain ⟨chronology⟩ := data.exists_rankedChronology collection infinite choice hK standard below oldRank level
  let target := chronology.linked infinite choice hK standard below oldRank
  have conditions := standard.to_conditions pairing unions powers separation hK
  have limit := conditions.rank_isLimit pairing unions powers separation infinite hK
  obtain ⟨row, ground, function, entries, rowRank⟩ := run.exists_limitTransitionRow limit oldRank
  have rowEntries : ∀ i z, ZFSet.pair (ZFSet.pair run.indices (run.key i)) z ∈ row ↔
      z = (chronology.cone.leg i).map.code := entries
  let extended := run.appendCone target chronology.cone ground function rowEntries chronology.cone_coverage
  have rank : ZFSet.rank extended.code < ZFSet.rank K :=
    run.appendCone_code_rank_lt target chronology.cone ground function rowEntries chronology.cone_coverage
      limit oldRank (target.code_rank_lt pairing unions powers separation infinite hK conditions) rowRank
  have preservedExtended : extended.PreservesOldProfiles :=
    run.appendCone_preservesOldProfiles preserved target chronology.cone ground function
      rowEntries chronology.cone_coverage
      (fun i => chronology.transition_preservesOldProfiles preserved i)
  have wholeEntries : ∀ i z, ZFSet.pair (ZFSet.pair run.indices (run.key i)) z ∈ extended.transitionGraph ↔
      z = (chronology.cone.leg i).map.code := by
    intro i z
    exact extended.transitionGraph_entry (show (i : WithTop I) ≤ ⊤ from le_top) z
  have rawCoverage := (run.limitCoverage_graph_iff chronology.cone wholeEntries).2 chronology.limitCoverage
  have indexEqual := run.appendCone_indices target chronology.cone ground function rowEntries chronology.cone_coverage
  have extendedIndexMember : extended.indices ∈
      M.groundOmegaOne pairing unions powers separation collection infinite := by
    rw [indexEqual]
    exact M.groundOmegaOne_successor pairing unions powers separation collection infinite indexMember
  refine ⟨data, chronology, target, extended, (fun _ => rfl), rfl, wholeEntries,
    chronology.limitCoverage, rawCoverage, rfl, rfl, preservedExtended,
    rfl, rfl, chronology.main_birth, chronology.code_member,
    indexEqual, extendedIndexMember,
    extended.code_ground, rank, level.prefix_mem_validMainPrefixes extended rank,
    level.prefix_mem_preservedMainPrefixes extended preservedExtended rank,
    run.appendCone_linked_old target chronology.cone ground function rowEntries chronology.cone_coverage,
    run.appendCone_linked_top target chronology.cone ground function rowEntries chronology.cone_coverage,
    run.appendCone_stageGraph target chronology.cone ground function rowEntries chronology.cone_coverage,
    run.appendCone_stageGraph_restrict target chronology.cone ground function rowEntries chronology.cone_coverage,
    run.appendCone_transitionGraph_restrict target chronology.cone ground function rowEntries chronology.cone_coverage,
    ?_, ?_, ?_⟩
  · intro i j before
    rfl
  · intro i
    exact ⟨rfl, rfl⟩
  · intro i x y entry
    exact data.point_strict_top i entry

end GroundMainPrefix

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixSelectedSuccessors
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

theorem exists_rankedAppendSelected
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (last : I) (greatest : ∀ i, i ≤ last) (preserved : run.PreservesOldProfiles)
    (oldRank : ZFSet.rank run.code < ZFSet.rank K)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K) (hLabels : Labels ∈ M.sets)
    (level : GroundMainCandidateLevel M K) {f targetCode z : ZFSet.{u}}
    (selected : f ⊆ M.taskBearingSuccessorRelation
      (M.linkedMainStageCandidates level.carrier K Labels C D rD) level.carrier K Labels C D rD)
    (entry : ZFSet.pair (run.linked last).code (ZFSet.pair targetCode z) ∈ f) :
    ∃ target : GroundLinkedMainStage M K Labels C D rD,
      ∃ step : GroundChronologicalMainTransition (run.diagram.stage last) target.main,
        ∃ covered : step.CoversOldBirths,
          ∃ extended : GroundMainPrefix M K Labels C D rD pairing unions powers separation (WithTop I),
            extended = run.appendLast last greatest target step covered ∧
            extended.PreservesOldProfiles ∧
            target.code = targetCode ∧ step.map.code = z ∧ step.PreservesOldProfiles ∧
            extended.code ∈ M.sets ∧ ZFSet.rank extended.code < ZFSet.rank K ∧
            extended.code ∈ level.validMainPrefixes Labels C D rD ∧
            extended.indices = insert run.indices run.indices ∧
            (∀ i : I, extended.linked (i : WithTop I) = run.linked i) ∧
            extended.linked ⊤ = target ∧
            extended.stageGraph = insert (ZFSet.pair run.indices targetCode) run.stageGraph ∧
            graphRestriction run.indices extended.stageGraph = run.stageGraph ∧
            graphRestriction (chronologyPairs run.indices) extended.transitionGraph = run.transitionGraph ∧
            (∀ (i j : I) (before : i ≤ j),
              (extended.diagram.transition (WithTop.coe_le_coe.mpr before)).map.code =
                (run.diagram.transition before).map.code) ∧
            (extended.diagram.transition (show (last : WithTop I) ≤ ⊤ from le_top)).map.code = z ∧
            (extended.diagram.transition (show (last : WithTop I) ≤ ⊤ from le_top)).map.points = step.map.points ∧
            (extended.diagram.transition (show (last : WithTop I) ≤ ⊤ from le_top)).map.actors = step.map.actors ∧
            TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega
              (run.linked last).code (extended.linked ⊤).code
              (extended.diagram.transition (show (last : WithTop I) ≤ ⊤ from le_top)).map.code := by
  have hC := (run.linked last).main.stage.columns_ground
  have hD := (run.linked last).main.stage.coordinates_ground
  have hrD := (run.linked last).main.stage.coordinate_order_ground
  have hS := M.linkedMainStageCandidates_mem pairing unions powers separation collection infinite
    level.carrier_ground hK hLabels hC hD hrD standard.1.1
  have subset : M.linkedMainStageCandidates level.carrier K Labels C D rD ⊆ level.carrier := by
    intro x hx
    exact ((M.mem_linkedMainStageCandidates level.carrier K Labels C D rD x).1 hx).1
  obtain ⟨_, targetMember, _, code⟩ :=
    (M.taskBearingSuccessorRelation_entry pairing unions powers separation collection infinite
      hS level.carrier_ground hK hLabels hC hD hrD standard.1.1 subset
      (run.linked last).code targetCode z).1 (selected entry)
  have conditions := standard.to_conditions pairing unions powers separation hK
  obtain ⟨target, step, covered, extended, equal, targetEqual, mapEqual, stepPreserved, rest⟩ :=
    run.exists_rankedAppendTaskBearing last greatest oldRank
      (conditions.rank_isLimit pairing unions powers separation infinite hK) level
      ((level.membership targetCode).1 (subset targetMember)).2 code
  refine ⟨target, step, covered, extended, equal, ?_, targetEqual, mapEqual, stepPreserved, rest⟩
  rw [equal]
  exact run.appendLast_preservesOldProfiles preserved last greatest target step covered stepPreserved

end PartitionPilot.Forcing.GroundMainPrefix

end

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

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_mainPrefixRecursionIndexFormula {n} (Omega z : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (mainPrefixRecursionIndexFormula Omega z) env ↔
      MainPrefixRecursionIndexCode (env Omega) (env z) := by
  rw [mainPrefixRecursionIndexFormula, realize_exBlock]
  have actual (fields : Fin 3 → ZFSet.{u}) (ground : ∀ j, fields j ∈ M.sets) :
      Realize M.sets (BoundedFormula.conj
        (BoundedFormula.mainPrefixTupleFormula (suffixIndex n 3 z)
          (prefixIndex n 3 0) (prefixIndex n 3 1) (prefixIndex n 3 2))
        (.conj (.mem (prefixIndex n 3 0) (suffixIndex n 3 Omega))
          (.neg (BoundedFormula.emptyFormula (prefixIndex n 3 0))))).toFormula
        (extendMany 3 fields env) ↔
      env z = mainPrefixCode (fields 0) (fields 1) (fields 2) ∧
        fields 0 ∈ env Omega ∧ fields 0 ≠ ∅ := by
    rw [BoundedFormula.realize_toFormula M _ _ (extendMany_members 3 fields env ground members)]
    simp only [BoundedFormula.Truth, BoundedFormula.truth_mainPrefixTupleFormula,
      BoundedFormula.truth_emptyFormula, extendMany_prefix, extendMany_suffix]
  constructor
  · rintro ⟨fields, ground, recognized⟩
    exact ⟨fields 0, fields 1, fields 2, (actual fields ground).1 recognized⟩
  · rintro ⟨T, S, E, equal, member, nonempty⟩
    have ground := M.mainPrefixCode_fields_mem (equal ▸ members z)
    let fields : Fin 3 → ZFSet.{u} := Fin.cases T (Fin.cases S (fun _ => E))
    have grounds : ∀ j, fields j ∈ M.sets :=
      Fin.cases ground.1 (Fin.cases ground.2.1 (fun _ => ground.2.2))
    exact ⟨fields, grounds, (actual fields grounds).2 ⟨equal, member, nonempty⟩⟩

end TransitiveGround

end

section
open SetFormula
universe u v

namespace GroundMainPrefix
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem appendLast_selectedStepCode (last : I) (greatest : ∀ i, i ≤ last)
    (target : GroundLinkedMainStage M K Labels C D rD)
    (step : GroundChronologicalMainTransition (run.diagram.stage last) target.main)
    (covered : step.CoversOldBirths) {b f : ZFSet.{u}}
    (indices : run.indices = insert b b) (lastKey : run.key last = b)
    (selected : ZFSet.pair (run.linked last).code (ZFSet.pair target.code step.map.code) ∈ f) :
    MainPrefixSelectedStepCode f run.code (run.appendLast last greatest target step covered).code := by
  let extended := run.appendLast last greatest target step covered
  refine ⟨b, run.stageGraph, run.transitionGraph, extended.stageGraph, extended.transitionGraph,
    (run.linked last).code, target.code, step.map.code, ?_, ?_, ?_, ?_, selected, ?_, ?_⟩
  · change mainPrefixCode run.indices run.stageGraph run.transitionGraph = _
    rw [indices]
  · change mainPrefixCode extended.indices extended.stageGraph extended.transitionGraph = _
    rw [run.appendLast_indices last greatest target step covered, indices]
  · apply (mainPrefixExtends_iff_restrictions run.graph_code extended.graph_code).2
    refine ⟨?_, run.appendLast_stageGraph_restrict last greatest target step covered,
      run.appendLast_transitionGraph_restrict last greatest target step covered⟩
    intro x hx
    rw [run.appendLast_indices last greatest target step covered]
    exact ZFSet.mem_insert_iff.2 (Or.inr hx)
  · rw [← lastKey]
    exact (run.stageGraph_entry last _).2 rfl
  · rw [← indices, run.appendLast_stageGraph last greatest target step covered]
    exact ZFSet.mem_insert_iff.2 (Or.inl rfl)
  · have entry := (extended.transitionGraph_entry (show (last : WithTop I) ≤ ⊤ from le_top)
      step.map.code).2 (congrArg (fun t => t.map.code)
        (run.appendLast_transition_last last greatest target step covered)).symm
    change ZFSet.pair (ZFSet.pair run.indices (run.key last)) step.map.code ∈ extended.transitionGraph at entry
    rw [indices, lastKey] at entry
    exact entry

end GroundMainPrefix

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

theorem recursionPrefixes_ground
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (hK : K ∈ M.sets) (ordinal : ordinalSetProperty K)
    {Omega Labels C D rD : ZFSet.{u}} (hOmega : Omega ∈ M.sets)
    (hLabels : Labels ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) :
    level.recursionPrefixes Omega Labels C D rD ∈ M.sets := by
  have hB := level.preservedMainPrefixes_ground pairing unions powers separation collection infinite
    hK ordinal hLabels hC hD hrD
  let params : Fin 1 → ZFSet.{u} := fun _ => Omega
  have ground : ∀ j, params j ∈ M.sets := fun _ => hOmega
  have separated := M.separation_mem separation (mainPrefixRecursionIndexFormula 1 0) params ground hB
  have equal : ZFSet.sep (fun z => Realize M.sets (mainPrefixRecursionIndexFormula 1 0)
      (extend z params)) (level.preservedMainPrefixes Labels C D rD) =
      level.recursionPrefixes Omega Labels C D rD := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, level.mem_recursionPrefixes]
    apply and_congr_right
    intro hz
    exact M.realize_mainPrefixRecursionIndexFormula 1 0 (extend z params)
      (Fin.cases (M.transitive hB hz) ground)
  exact equal ▸ separated

theorem prefix_mem_recursionPrefixes
    {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
    {unions : Realize M.sets SetFormula.union Fin.elim0}
    {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
    {Omega Labels C D rD : ZFSet.{u}} {I : Type v} [Small.{u} I] [Preorder I]
    (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)
    (preserved : run.PreservesOldProfiles) (rank : ZFSet.rank run.code < ZFSet.rank K)
    (indices : run.indices ∈ Omega) (nonempty : run.indices ≠ ∅) :
    run.code ∈ level.recursionPrefixes Omega Labels C D rD :=
  level.mem_recursionPrefixes.2 ⟨level.prefix_mem_preservedMainPrefixes run preserved rank,
    mainPrefixRecursionIndexCode_iff.2 ⟨indices, nonempty⟩⟩

theorem exists_prefix_of_mem_recursionPrefixes
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {Omega Labels C D rD z : ZFSet.{u}}
    (member : z ∈ level.recursionPrefixes Omega Labels C D rD) :
    ∃ T ∈ M.sets, T ∈ Omega ∧ T ≠ ∅ ∧ Nonempty (SetMembers T) ∧
      ∃ ordinal : ordinalSetProperty T,
        letI := ordinalMainIndexPreorder ordinal
        ∃ run : GroundMainPrefix M K Labels C D rD pairing unions powers separation (SetMembers T),
          run.indices = T ∧ run.code = z ∧ run.PreservesOldProfiles ∧
          ZFSet.rank run.code < ZFSet.rank K := by
  obtain ⟨candidate, indexCode⟩ := level.mem_recursionPrefixes.1 member
  obtain ⟨T, hT, ordinal, run, indices, equal, preserved, rank⟩ :=
    level.exists_preservedPrefix_of_mem pairing unions powers separation candidate
  let := ordinalMainIndexPreorder ordinal
  have index : run.indices ∈ Omega ∧ run.indices ≠ ∅ :=
    mainPrefixRecursionIndexCode_iff.1 (equal.symm ▸ indexCode)
  have actual : T ∈ Omega ∧ T ≠ ∅ := indices ▸ index
  have inhabited : Nonempty (SetMembers T) := by
    classical
    by_contra empty
    apply actual.2
    apply (ZFSet.eq_empty T).2
    intro x hx
    exact empty ⟨SetMembers.ofMem x hx⟩
  exact ⟨T, hT, actual.1, actual.2, inhabited, ordinal, run, indices, equal, preserved, rank⟩

end GroundMainCandidateLevel
end

namespace GroundMainPrefix
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem exists_selectedStepCode
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K) (hLabels : Labels ∈ M.sets)
    (preserved : run.PreservesOldProfiles) (oldRank : ZFSet.rank run.code < ZFSet.rank K)
    (member : run.indices ∈ M.groundOmegaOne pairing unions powers separation collection infinite)
    {b f : ZFSet.{u}} (indices : run.indices = insert b b)
    (level : GroundMainCandidateLevel M K)
    (function : ZFSet.IsFunc (M.linkedMainStageCandidates level.carrier K Labels C D rD)
      (ZFSet.prod level.carrier level.carrier) f)
    (selected : f ⊆ M.taskBearingSuccessorRelation
      (M.linkedMainStageCandidates level.carrier K Labels C D rD) level.carrier K Labels C D rD) :
    ∃ next ∈ M.sets,
      next ∈ level.recursionPrefixes
        (M.groundOmegaOne pairing unions powers separation collection infinite) Labels C D rD ∧
      MainPrefixSelectedStepCode f run.code next := by
  have lastMember : b ∈ run.indices := by
    rw [indices]
    exact ZFSet.mem_insert_iff.2 (Or.inl rfl)
  obtain ⟨last, lastKey⟩ := ZFSet.mem_range.1 lastMember
  have greatest : ∀ i, i ≤ last := by
    intro i
    apply (run.key_order i last).2
    rw [lastKey]
    have hi : run.key i ∈ run.indices := ZFSet.mem_range.2 ⟨i, rfl⟩
    rw [indices] at hi
    exact ZFSet.mem_insert_iff.1 hi
  have sourceMember : (run.linked last).code ∈
      M.linkedMainStageCandidates level.carrier K Labels C D rD :=
    (M.mem_linkedMainStageCandidates level.carrier K Labels C D rD _).2
      ⟨(level.membership _).2 ⟨(run.linked last).code_ground pairing,
        (run.linkedCode_rank_lt_code last).trans oldRank⟩, run.linked last, rfl⟩
  have graph : FunctionGraphOn (M.linkedMainStageCandidates level.carrier K Labels C D rD) f :=
    ⟨ZFSet.prod level.carrier level.carrier, function⟩
  obtain ⟨output, entry⟩ := graph.total sourceMember
  obtain ⟨targetCode, _, z, _, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.pair_mem_prod.1 (function.1 entry)).2
  obtain ⟨target, step, covered, extended, equal, profiles, targetEqual, mapEqual,
      _, ground, rank, _, extendedIndices, _⟩ :=
    run.exists_rankedAppendSelected collection infinite last greatest preserved oldRank hK standard
      hLabels level selected entry
  have chosen : ZFSet.pair (run.linked last).code (ZFSet.pair target.code step.map.code) ∈ f := by
    rw [targetEqual, mapEqual]
    exact entry
  have branch := run.appendLast_selectedStepCode last greatest target step covered indices lastKey chosen
  rw [← equal] at branch
  have newMember : extended.indices ∈ M.groundOmegaOne pairing unions powers separation collection infinite := by
    rw [extendedIndices]
    exact M.groundOmegaOne_successor pairing unions powers separation collection infinite member
  have nonempty : extended.indices ≠ ∅ := by
    rw [extendedIndices]
    exact setSuccessor_ne_empty run.indices
  exact ⟨extended.code, ground, level.prefix_mem_recursionPrefixes extended profiles rank newMember nonempty, branch⟩

end GroundMainPrefix

open SetFormula SetRealization
universe u v w

namespace GroundMainPrefix
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem limitStepCode_of_fields {J : Type w} [Small.{u} J] [Preorder J]
    (target : GroundLinkedMainStage M K Labels C D rD)
    (extended : GroundMainPrefix M K Labels C D rD pairing unions powers separation J)
    (indices : extended.indices = insert run.indices run.indices)
    (extension : MainPrefixExtends run.code extended.code)
    (entry : ZFSet.pair run.indices target.code ∈ extended.stageGraph)
    (coverage : MainLimitCoverageGraphCode run.indices run.stageGraph extended.transitionGraph
      target.main.stage.carrier target.main.stage.actors target.main.stage.order
      target.main.stage.top target.main.cutoff target.main.birth) :
    MainPrefixLimitStepCode M K Labels C D rD ZFSet.omega run.code extended.code := by
  let fields : Fin 32 → ZFSet.{u} := Fin.cases run.indices (Fin.cases run.stageGraph
    (Fin.cases run.transitionGraph (Fin.cases extended.stageGraph (Fin.cases extended.transitionGraph
      (Fin.cases target.code (Fin.cases target.main.birth (Fin.cases extended.indices target.rawFields)))))))
  have ground : ∀ j, fields j ∈ M.sets := Fin.cases run.indices_ground (Fin.cases run.stages_ground
    (Fin.cases run.transitions_ground (Fin.cases extended.stages_ground (Fin.cases extended.transitions_ground
      (Fin.cases (target.code_ground pairing) (Fin.cases target.main.birth_ground
        (Fin.cases extended.indices_ground (target.rawFields_ground pairing))))))))
  have targetFields : mainPrefixLimitTargetFields fields = target.rawFields := by
    funext j
    have same : Fin.natAdd 8 j = j.succ.succ.succ.succ.succ.succ.succ.succ := by
      apply Fin.ext
      change 8 + j.val = j.val + 8
      exact Nat.add_comm 8 j.val
    change fields (Fin.natAdd 8 j) = target.rawFields j
    rw [same]
    rfl
  refine ⟨fields, ground, ?_⟩
  unfold MainPrefixLimitStepRawCode
  rw [targetFields]
  exact ⟨indices, rfl, rfl, extension, entry, target.rawFields_code,
    target.rawFields_birth_entry, coverage⟩

theorem exists_limitStepCode (preserved : run.PreservesOldProfiles) (i₀ : I)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (columns_eq : C = M.groundOmegaOne pairing unions powers separation collection infinite)
    (indexMember : run.indices ∈ M.groundOmegaOne pairing unions powers separation collection infinite)
    (oldRank : ZFSet.rank run.code < ZFSet.rank K)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (level : GroundMainCandidateLevel M K) :
    ∃ next ∈ M.sets,
      next ∈ level.recursionPrefixes
        (M.groundOmegaOne pairing unions powers separation collection infinite) Labels C D rD ∧
      MainPrefixLimitStepCode M K Labels C D rD ZFSet.omega run.code next := by
  obtain ⟨data, chronology, target, extended, _, _, _, _, coverage, _, _, profiles,
      _, _, _, _, indices, indexMember', ground, rank, _, _, _, _, stageGraph,
      stageRestriction, transitionRestriction, _⟩ :=
    run.exists_rawCoveredPreservedAppendLimit preserved i₀ collection infinite choice columns_eq
      indexMember oldRank hK standard level
  have extension : MainPrefixExtends run.code extended.code := by
    apply (mainPrefixExtends_iff_restrictions run.graph_code extended.graph_code).2
    refine ⟨?_, stageRestriction, transitionRestriction⟩
    intro x hx
    rw [indices]
    exact ZFSet.mem_insert_iff.2 (Or.inr hx)
  have entry : ZFSet.pair run.indices target.code ∈ extended.stageGraph := by
    rw [stageGraph]
    exact ZFSet.mem_insert_iff.2 (Or.inl rfl)
  have nonempty : extended.indices ≠ ∅ := by
    rw [indices]
    exact setSuccessor_ne_empty run.indices
  exact ⟨extended.code, ground,
    level.prefix_mem_recursionPrefixes extended profiles rank indexMember' nonempty,
    run.limitStepCode_of_fields target extended indices extension entry coverage⟩

end GroundMainPrefix

end PartitionPilot.Forcing

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

namespace BoundedFormula
open SetFormula
universe u

theorem truth_nonzeroLimitOrdinalFormula {n} (T : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (nonzeroLimitOrdinalFormula T) env ↔ NonzeroLimitOrdinalCode (env T) := by
  simp only [nonzeroLimitOrdinalFormula, Truth, truth_emptyFormula, truth_exMem]
  rfl

theorem realize_nonzeroLimitOrdinalFormula (M : TransitiveGround.{u}) {n}
    (T : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (nonzeroLimitOrdinalFormula T).toFormula env ↔
      NonzeroLimitOrdinalCode (env T) :=
  (realize_toFormula M _ env members).trans (truth_nonzeroLimitOrdinalFormula T env)

end BoundedFormula

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

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_mainPrefixLimitStepRawFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) {n} (K Labels C D rD N old next : Fin n)
    (w : Fin 32 → Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (mainPrefixLimitStepRawFormula K Labels C D rD N old next w) env ↔
      MainPrefixLimitStepRawCode M (env K) (env Labels) (env C) (env D) (env rD) (env N)
        (env old) (env next) (fun j => env (w j)) := by
  have linked := M.realize_linkedMainStageRawFormula pairing unions powers separation collection
    K Labels C D rD N (w 5) (mainPrefixLimitTargetFields w) env members omega ordinal
  have extension := M.realize_mainPrefixExtensionFormula old next env members
  simp only [mainPrefixLimitStepRawFormula, Realize, BoundedFormula.realize_toFormula M _ env members,
    BoundedFormula.truth_successorFormula, BoundedFormula.truth_mainPrefixTupleFormula,
    extension, BoundedFormula.truth_pairMembershipFormula, linked,
    BoundedFormula.truth_mainLimitCoverageFormula]
  rfl

theorem realize_mainPrefixLimitStepFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) {n} (K Labels C D rD N old next : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (mainPrefixLimitStepFormula K Labels C D rD N old next) env ↔
      MainPrefixLimitStepCode M (env K) (env Labels) (env C) (env D) (env rD) (env N)
        (env old) (env next) := by
  rw [mainPrefixLimitStepFormula, realize_exBlock]
  have actual (w : Fin 32 → ZFSet.{u}) (ground : ∀ j, w j ∈ M.sets) :=
    M.realize_mainPrefixLimitStepRawFormula pairing unions powers separation collection
      (suffixIndex n 32 K) (suffixIndex n 32 Labels) (suffixIndex n 32 C) (suffixIndex n 32 D)
      (suffixIndex n 32 rD) (suffixIndex n 32 N) (suffixIndex n 32 old) (suffixIndex n 32 next)
      (prefixIndex n 32) (extendMany 32 w env) (extendMany_members 32 w env ground members)
      (by simpa only [extendMany_suffix] using omega)
      (by simpa only [extendMany_suffix] using ordinal)
  simp only [extendMany_prefix, extendMany_suffix] at actual
  exact ⟨fun ⟨w, ground, recognized⟩ => ⟨w, ground, (actual w ground).1 recognized⟩,
    fun ⟨w, ground, raw⟩ => ⟨w, ground, (actual w ground).2 raw⟩⟩

end TransitiveGround

namespace BoundedFormula

theorem truth_mainPrefixSelectedStepBody {n} (f old next : Fin n) (v : Fin 10 → Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (mainPrefixSelectedStepBody f old next v) env ↔
      env (v 8) = insert (env (v 0)) (env (v 0)) ∧
      env (v 9) = insert (env (v 8)) (env (v 8)) ∧
      env old = mainPrefixCode (env (v 8)) (env (v 1)) (env (v 2)) ∧
      env next = mainPrefixCode (env (v 9)) (env (v 3)) (env (v 4)) ∧
      (env (v 8) ⊆ env (v 9) ∧ env (v 1) ⊆ env (v 3) ∧ env (v 2) ⊆ env (v 4)) ∧
      ZFSet.pair (env (v 0)) (env (v 5)) ∈ env (v 1) ∧
      ZFSet.pair (env (v 5)) (ZFSet.pair (env (v 6)) (env (v 7))) ∈ env f ∧
      ZFSet.pair (env (v 8)) (env (v 6)) ∈ env (v 3) ∧
      ZFSet.pair (ZFSet.pair (env (v 8)) (env (v 0))) (env (v 7)) ∈ env (v 4) := by
  simp only [mainPrefixSelectedStepBody, Truth, truth_successorFormula,
    truth_mainPrefixTupleFormula, truth_mainPrefixFieldExtensionFormula,
    truth_pairMembershipFormula, truth_rightTripleMembershipFormula, truth_tripleMembershipFormula]

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_mainPrefixSelectedStepFormula {n} (f old next : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (mainPrefixSelectedStepFormula f old next) env ↔
      MainPrefixSelectedStepCode (env f) (env old) (env next) := by
  rw [mainPrefixSelectedStepFormula, realize_exBlock]
  have actual (v : Fin 10 → ZFSet.{u}) (ground : ∀ j, v j ∈ M.sets) :=
    (BoundedFormula.realize_toFormula M _ (extendMany 10 v env)
      (extendMany_members 10 v env ground members)).trans
      (BoundedFormula.truth_mainPrefixSelectedStepBody
        (suffixIndex n 10 f) (suffixIndex n 10 old) (suffixIndex n 10 next)
        (prefixIndex n 10) (extendMany 10 v env))
  simp only [extendMany_prefix, extendMany_suffix] at actual
  constructor
  · rintro ⟨v, ground, recognized⟩
    obtain ⟨first, second, oldCode, nextCode, extension, source, selected, target, crossing⟩ :=
      (actual v ground).1 recognized
    refine ⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, ?_, ?_, ?_, source, selected, ?_, ?_⟩
    · simpa only [first] using oldCode
    · simpa only [second, first] using nextCode
    · rw [oldCode, nextCode]
      exact mainPrefixExtends_iff.2 extension
    · simpa only [first] using target
    · simpa only [first] using crossing
  · rintro ⟨b, S, E, S', E', a, target, z, oldCode, nextCode,
      extension, source, selected, targetEntry, crossing⟩
    have left := M.mainPrefixCode_fields_mem (oldCode ▸ members old)
    have right := M.mainPrefixCode_fields_mem (nextCode ▸ members next)
    have sourceGround := M.transitive left.2.1 source
    have selectedGround := M.transitive (members f) selected
    let v : Fin 10 → ZFSet.{u} := Fin.cases b (Fin.cases S (Fin.cases E
      (Fin.cases S' (Fin.cases E' (Fin.cases a (Fin.cases target (Fin.cases z
        (Fin.cases (insert b b) (fun _ => insert (insert b b) (insert b b))))))))))
    have ground : ∀ j, v j ∈ M.sets := Fin.cases (M.pair_left sourceGround)
      (Fin.cases left.2.1 (Fin.cases left.2.2 (Fin.cases right.2.1 (Fin.cases right.2.2
      (Fin.cases (M.pair_right sourceGround) (Fin.cases (M.pair_left (M.pair_right selectedGround))
      (Fin.cases (M.pair_right (M.pair_right selectedGround)) (Fin.cases left.1 (fun _ => right.1)))))))))
    rw [oldCode, nextCode] at extension
    exact ⟨v, ground, (actual v ground).2 ⟨rfl, rfl, oldCode, nextCode,
      mainPrefixExtends_iff.1 extension, source, selected, targetEntry, crossing⟩⟩

end TransitiveGround

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_mainPrefixConditionalStepFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) {n}
    (K Labels C D rD N f old next : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) (omega : env N = ZFSet.omega)
    (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (mainPrefixConditionalStepFormula K Labels C D rD N f old next) env ↔
      MainPrefixConditionalStepCode M (env K) (env Labels) (env C) (env D) (env rD)
        (env N) (env f) (env old) (env next) := by
  rw [mainPrefixConditionalStepFormula, realize_disj,
    M.realize_mainPrefixSelectedStepFormula f old next env members, realize_exBlock]
  apply or_congr Iff.rfl
  let outer := suffixIndex n 3
  let field := prefixIndex n 3
  have actual (w : Fin 3 → ZFSet.{u}) (ground : ∀ j, w j ∈ M.sets) :
      Realize M.sets (.conj
        (BoundedFormula.mainPrefixTupleFormula (outer old) (field 0) (field 1) (field 2)).toFormula
        (.conj (BoundedFormula.nonzeroLimitOrdinalFormula (field 0)).toFormula
          (mainPrefixLimitStepFormula (outer K) (outer Labels) (outer C) (outer D)
            (outer rD) (outer N) (outer old) (outer next)))) (extendMany 3 w env) ↔
      env old = mainPrefixCode (w 0) (w 1) (w 2) ∧ NonzeroLimitOrdinalCode (w 0) ∧
        MainPrefixLimitStepCode M (env K) (env Labels) (env C) (env D) (env rD) (env N)
          (env old) (env next) := by
    have mems := extendMany_members 3 w env ground members
    change (Realize M.sets _ _ ∧ Realize M.sets _ _ ∧ Realize M.sets _ _) ↔ _
    rw [BoundedFormula.realize_mainPrefixTupleFormula M _ _ _ _ _ mems,
      BoundedFormula.realize_nonzeroLimitOrdinalFormula M _ _ mems,
      M.realize_mainPrefixLimitStepFormula pairing unions powers separation collection
        _ _ _ _ _ _ _ _ _ mems (by simpa only [outer, extendMany_suffix] using omega)
          (by simpa only [outer, extendMany_suffix] using ordinal)]
    simp only [outer, field, extendMany_suffix, extendMany_prefix]
  constructor
  · rintro ⟨w, ground, recognized⟩
    exact ⟨w 0, w 1, w 2, (actual w ground).1 recognized⟩
  · rintro ⟨T, S, E, oldCode, nonzero, code⟩
    have fields := M.mainPrefixCode_fields_mem (oldCode ▸ members old)
    let w : Fin 3 → ZFSet.{u} := Fin.cases T (Fin.cases S (fun _ => E))
    have ground : ∀ j, w j ∈ M.sets := Fin.cases fields.1 (Fin.cases fields.2.1 (fun _ => fields.2.2))
    exact ⟨w, ground, (actual w ground).2 ⟨oldCode, nonzero, code⟩⟩

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundMainConditionalTotality
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

theorem mainPrefixConditionalRelation_ground
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {S K Labels C D rD N f : ZFSet.{u}} (hS : S ∈ M.sets)
    (hK : K ∈ M.sets) (hLabels : Labels ∈ M.sets) (hC : C ∈ M.sets)
    (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) (hN : N ∈ M.sets) (hf : f ∈ M.sets) :
    M.mainPrefixConditionalRelation S K Labels C D rD N f ∈ M.sets :=
  M.definableRelation_mem pairing unions powers separation _ _
    (Fin.cases hK (Fin.cases hLabels (Fin.cases hC (Fin.cases hD (Fin.cases hrD
      (Fin.cases hN (Fin.cases hf (fun j => Fin.elim0 j)))))))) hS hS

theorem mainPrefixConditionalRelation_entry
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    {S K Labels C D rD N f : ZFSet.{u}} (hS : S ∈ M.sets)
    (hK : K ∈ M.sets) (hLabels : Labels ∈ M.sets) (hC : C ∈ M.sets)
    (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) (hN : N ∈ M.sets) (hf : f ∈ M.sets)
    (omega : N = ZFSet.omega) (ordinal : ordinalSetProperty K) (old next : ZFSet.{u}) :
    ZFSet.pair old next ∈ M.mainPrefixConditionalRelation S K Labels C D rD N f ↔
      old ∈ S ∧ next ∈ S ∧ MainPrefixConditionalStepCode M K Labels C D rD N f old next := by
  rw [mainPrefixConditionalRelation, M.pair_mem_definableRelation]
  apply and_congr_right
  intro oldMember
  apply and_congr_right
  intro nextMember
  exact M.realize_mainPrefixConditionalStepFormula pairing unions powers separation collection
    2 3 4 5 6 7 8 0 1
    (extend old (extend next (mainPrefixConditionalParams K Labels C D rD N f)))
    (Fin.cases (M.transitive hS oldMember) (Fin.cases (M.transitive hS nextMember)
      (Fin.cases hK (Fin.cases hLabels (Fin.cases hC (Fin.cases hD (Fin.cases hrD
        (Fin.cases hN (Fin.cases hf (fun j => Fin.elim0 j)))))))))) omega ordinal

theorem choose_mainPrefixConditionalSteps
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {S K Labels C D rD N f : ZFSet.{u}} (hS : S ∈ M.sets)
    (hK : K ∈ M.sets) (hLabels : Labels ∈ M.sets) (hC : C ∈ M.sets)
    (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) (hN : N ∈ M.sets) (hf : f ∈ M.sets)
    (omega : N = ZFSet.omega) (ordinal : ordinalSetProperty K)
    (total : ∀ old ∈ S, ∃ next ∈ S, MainPrefixConditionalStepCode M K Labels C D rD N f old next) :
    ∃ g ∈ M.sets, ZFSet.IsFunc S S g ∧
      g ⊆ M.mainPrefixConditionalRelation S K Labels C D rD N f ∧
      ∀ old next, ZFSet.pair old next ∈ g →
        next ∈ S ∧ MainPrefixConditionalStepCode M K Labels C D rD N f old next := by
  have entries := M.mainPrefixConditionalRelation_entry pairing unions powers separation collection
    hS hK hLabels hC hD hrD hN hf omega ordinal
  obtain ⟨g, ground, function, included⟩ := M.uniformize_relation pairing unions powers separation choice
    hS hS (M.mainPrefixConditionalRelation_ground pairing unions powers separation
      hS hK hLabels hC hD hrD hN hf) (by
        intro old oldMember
        obtain ⟨next, nextMember, code⟩ := total old oldMember
        exact ⟨next, nextMember, (entries old next).2 ⟨oldMember, nextMember, code⟩⟩)
  exact ⟨g, ground, function, included, fun old next entry =>
    ((entries old next).1 (included entry)).2⟩

end TransitiveGround
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundMainCandidateLevel
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}
variable (level : GroundMainCandidateLevel M K)

theorem conditionalSteps_total
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {Labels C D rD f : ZFSet.{u}} (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (hLabels : Labels ∈ M.sets)
    (columns_eq : C = M.groundOmegaOne pairing unions powers separation collection infinite)
    (function : ZFSet.IsFunc (M.linkedMainStageCandidates level.carrier K Labels C D rD)
      (ZFSet.prod level.carrier level.carrier) f)
    (selected : f ⊆ M.taskBearingSuccessorRelation
      (M.linkedMainStageCandidates level.carrier K Labels C D rD) level.carrier K Labels C D rD)
    (old : ZFSet.{u})
    (member : old ∈ level.recursionPrefixes
      (M.groundOmegaOne pairing unions powers separation collection infinite) Labels C D rD) :
    ∃ next ∈ level.recursionPrefixes
      (M.groundOmegaOne pairing unions powers separation collection infinite) Labels C D rD,
      MainPrefixConditionalStepCode M K Labels C D rD ZFSet.omega f old next := by
  obtain ⟨T, _, indexMember, nonempty, inhabited, ordinal, run, indices, equal, preserved, rank⟩ :=
    level.exists_prefix_of_mem_recursionPrefixes pairing unions powers separation member
  let := ordinalMainIndexPreorder ordinal
  have actualIndex : run.indices ∈ M.groundOmegaOne pairing unions powers separation collection infinite :=
    indices.symm ▸ indexMember
  rcases ordinal_successor_or_nonzeroLimit ordinal nonempty with successor | limit
  · obtain ⟨b, _, successor⟩ := successor
    obtain ⟨next, _, nextMember, code⟩ := run.exists_selectedStepCode collection infinite hK standard hLabels
      preserved rank actualIndex (indices.trans successor) level function selected
    exact ⟨next, nextMember, Or.inl (equal ▸ code)⟩
  · obtain ⟨i₀⟩ := inhabited
    obtain ⟨next, _, nextMember, code⟩ := run.exists_limitStepCode preserved i₀ collection infinite choice
      columns_eq actualIndex rank hK standard level
    refine ⟨next, nextMember, Or.inr ⟨T, run.stageGraph, run.transitionGraph, ?_, limit, equal ▸ code⟩⟩
    exact equal.symm.trans (congrArg
      (fun U => mainPrefixCode U run.stageGraph run.transitionGraph) indices)

theorem exists_groundConditionalPrefixFunction_oai
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {Labels C D rD f : ZFSet.{u}} (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (hLabels : Labels ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (columns_eq : C = M.groundOmegaOne pairing unions powers separation collection infinite)
    (hf : f ∈ M.sets)
    (function : ZFSet.IsFunc (M.linkedMainStageCandidates level.carrier K Labels C D rD)
      (ZFSet.prod level.carrier level.carrier) f)
    (selected : f ⊆ M.taskBearingSuccessorRelation
      (M.linkedMainStageCandidates level.carrier K Labels C D rD) level.carrier K Labels C D rD) :
    let S := level.recursionPrefixes
      (M.groundOmegaOne pairing unions powers separation collection infinite) Labels C D rD
    ∃ g ∈ M.sets, ZFSet.IsFunc S S g ∧
      g ⊆ M.mainPrefixConditionalRelation S K Labels C D rD ZFSet.omega f ∧
      ∀ old next, ZFSet.pair old next ∈ g →
        next ∈ S ∧ MainPrefixConditionalStepCode M K Labels C D rD ZFSet.omega f old next := by
  have hOmega := M.transitive hK
    (standard.groundOmegaOne_mem pairing unions powers separation collection infinite hK)
  have hC : C ∈ M.sets := columns_eq.symm ▸ hOmega
  have hS := level.recursionPrefixes_ground pairing unions powers separation collection infinite
    hK standard.1.1 hOmega hLabels hC hD hrD
  exact M.choose_mainPrefixConditionalSteps pairing unions powers separation collection choice
    hS hK hLabels hC hD hrD (M.omega_mem separation infinite) hf rfl standard.1.1
    (level.conditionalSteps_total pairing unions powers separation collection infinite choice
      hK standard hLabels columns_eq function selected)

end PartitionPilot.Forcing.GroundMainCandidateLevel

end

end OAI
end

theorem solution.{u} : type_of% @OAI.PartitionPilot.Forcing.GroundMainCandidateLevel.exists_groundConditionalPrefixFunction_oai.{u} := @OAI.PartitionPilot.Forcing.GroundMainCandidateLevel.exists_groundConditionalPrefixFunction_oai.{u}
