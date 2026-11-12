-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralTrace_commonPowerAntichains
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:12:56.331756+00:00
-- url     : https://prove2.me/submissions/128ad4bc-5007-4235-a48b-8c33cee97cc7

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

theorem compatible_include_iff (p : Upper) (q : Lower) :
    Compatible p (inclusion q) ↔ Compatible (restriction p) q := by
  constructor
  · rintro ⟨r, rp, rq⟩
    exact ⟨restriction r, restriction.monotone rp, (projection.le_include_iff r q).1 rq⟩
  · rintro ⟨q', below, included⟩
    obtain ⟨r, rp, equal⟩ := projection.lift p q' below
    refine ⟨r, rp, (projection.le_include_iff r q).2 ?_⟩
    exact equal.symm ▸ included

theorem included_compatible_iff (p q : Lower) :
    Compatible (inclusion p) (inclusion q) ↔ Compatible p q := by
  rw [projection.compatible_include_iff, projection.retract]

theorem predense_inclusion {E : Set Lower}
    (predense : ∀ q : Lower, ∃ r ∈ E, Compatible q r) :
    ∀ p : Upper, ∃ r ∈ E, Compatible p (inclusion r) := by
  intro p
  obtain ⟨r, member, compatible⟩ := predense (restriction p)
  exact ⟨r, member, (projection.compatible_include_iff p r).2 compatible⟩

end CompleteProjection
end



namespace CompleteProjection
open SetRealization
universe u
variable {Upper Lower : Type u} [PartialOrder Upper] [PartialOrder Lower]
variable {restriction : Upper →o Lower} {inclusion : Lower ↪o Upper}
variable (projection : CompleteProjection restriction inclusion)
include projection

theorem predense_inclusion_iff {E : Set Lower} :
    (∀ p : Upper, ∃ r ∈ E, Compatible p (inclusion r)) ↔
      (∀ q : Lower, ∃ r ∈ E, Compatible q r) := by
  constructor
  · intro predense q
    obtain ⟨r, member, common⟩ := predense (inclusion q)
    exact ⟨r, member, (projection.included_compatible_iff q r).1 common⟩
  · exact projection.predense_inclusion

theorem raw_predense_restriction (s : Presentation Upper) (t : Presentation Lower)
    (unchanged : ∀ q, s.encode (inclusion q) = t.encode q)
    {A : ZFSet.{u}} (within : A ⊆ t.carrier)
    (predense : ∀ q ∈ s.carrier, ∃ p ∈ A, ∃ r ∈ s.carrier,
      ZFSet.pair r q ∈ s.conditionOrder ∧ ZFSet.pair r p ∈ s.conditionOrder) :
    ∀ q ∈ t.carrier, ∃ p ∈ A, ∃ r ∈ t.carrier,
      ZFSet.pair r q ∈ t.conditionOrder ∧ ZFSet.pair r p ∈ t.conditionOrder := by
  have upper : ∀ p : Upper, ∃ q, t.encode q ∈ A ∧ Compatible p (inclusion q) := by
    intro p
    obtain ⟨x, hx, z, hz, zp, zx⟩ := predense (s.encode p) (s.encode_mem p)
    obtain ⟨q, qCode⟩ := (t.mem_carrier x).1 (within hx)
    obtain ⟨r, rCode⟩ := (s.mem_carrier z).1 hz
    refine ⟨q, qCode.symm ▸ hx, r, ?_, ?_⟩
    · apply (s.pair_mem_conditionOrder r p).1
      rwa [rCode]
    · apply (s.pair_mem_conditionOrder r (inclusion q)).1
      rwa [rCode, unchanged q, qCode]
  have lower := (projection.predense_inclusion_iff (E := {q | t.encode q ∈ A})).1 upper
  intro x hx
  obtain ⟨q, qCode⟩ := (t.mem_carrier x).1 hx
  obtain ⟨p, hp, r, rq, rp⟩ := lower q
  refine ⟨t.encode p, hp, t.encode r, t.encode_mem r, ?_,
    (t.pair_mem_conditionOrder r p).2 rp⟩
  rw [← qCode]
  exact (t.pair_mem_conditionOrder r q).2 rq

end CompleteProjection

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_NameRenameSteps
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem ordinaryMembershipDecisions_subset (Q order sigma tau : ZFSet.{u}) :
    M.ordinaryMembershipDecisions Q order sigma tau ⊆ Q :=
  fun _ h => (ZFSet.mem_sep.1 h).1

variable {P : Type u} [Preorder P] (s : Presentation P)

theorem realize_ordinaryMembershipDecisionFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {n : Nat} (ci oi pi si ti : Fin n) (env : Fin n → ZFSet.{u})
    (sigma tau : (M.nameDomain s).names) (p : P)
    (hc : env ci = s.carrier) (ho : env oi = s.conditionOrder)
    (hp : env pi = s.encode p) (hs : env si = sigma.val.val) (ht : env ti = tau.val.val) :
    Realize M.sets (ordinaryMembershipDecisionFormula ci oi pi si ti) env ↔
      Name.ForcesMem p sigma.val tau.val ∨ ∀ q, q ≤ p → ¬ Name.ForcesMem q sigma.val tau.val := by
  rw [ordinaryMembershipDecisionFormula, realize_disj]
  let names : Assignment (M.nameDomain s) 2 := extend sigma (extend tau Fin.elim0)
  have meaning (phi : SetFormula 2) := M.realize_ordinaryGroundForcing s pairing unions powers
    separation collection carrier order (0 : Fin 2) 1 phi (extend ci (extend oi Fin.elim0)) pi
    (extend si (extend ti Fin.elim0)) env hc ho p names hp
    (Fin.cases hs (Fin.cases ht (fun i => Fin.elim0 i)))
  exact or_congr (meaning (.mem 0 1)) (meaning (.neg (.mem 0 1)))

theorem ordinaryMembershipDecisions_entry
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (sigma tau : (M.nameDomain s).names) (p : P) :
    s.encode p ∈ M.ordinaryMembershipDecisions s.carrier s.conditionOrder sigma.val.val tau.val.val ↔
      Name.ForcesMem p sigma.val tau.val ∨ ∀ q, q ≤ p → ¬ Name.ForcesMem q sigma.val tau.val := by
  rw [ordinaryMembershipDecisions, ZFSet.mem_sep, and_iff_right (s.encode_mem p)]
  exact M.realize_ordinaryMembershipDecisionFormula s pairing unions powers separation collection
    carrier order 1 2 0 3 4 _ sigma tau p rfl rfl rfl rfl rfl

theorem ordinaryMembershipDecisions_dense
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (sigma tau : (M.nameDomain s).names) :
    ∀ p ∈ s.carrier, ∃ q ∈ M.ordinaryMembershipDecisions s.carrier s.conditionOrder
      sigma.val.val tau.val.val, ZFSet.pair q p ∈ s.conditionOrder := by
  intro z hz
  obtain ⟨p, rfl⟩ := (s.mem_carrier z).1 hz
  obtain ⟨q, below, decided⟩ := decisionWitness_dense (M.nameDomain s) (.mem 0 1)
    (extend sigma (extend tau Fin.elim0)) p
  exact ⟨s.encode q,
    (M.ordinaryMembershipDecisions_entry s pairing unions powers separation collection carrier order
      sigma tau q).2 decided, (s.pair_mem_conditionOrder q p).2 below⟩

end TransitiveGround
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

namespace GroundBelow
variable {M N : TransitiveGround.{u}} {A B K L : ZFSet.{u}}

theorem empty_iff (hK : K ∈ M.sets) : GroundBelow M ∅ K ↔ K.Nonempty := by
  constructor
  · rintro ⟨β, hβ, _⟩
    exact ⟨β, hβ⟩
  · rintro ⟨β, hβ⟩
    exact ⟨β, hβ, M.empty_groundEmbeddable β ⟨K, hK⟩⟩

end GroundBelow

end PartitionPilot.Forcing



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

end TransitiveGround

end PartitionPilot.Forcing



end

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_RepresentativeIndexSteps
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
universe u

theorem mem_assignmentIndices (I T A t : ZFSet.{u}) :
    t ∈ assignmentIndices I T A ↔
      t ∈ I ∧ ∃ u ∈ T, ∃ w ∈ T, stageOneAssignment t u w ∈ A := by
  rw [assignmentIndices, mem_relationImage]
  constructor
  · rintro ⟨ht, z, hz, entry⟩
    obtain ⟨i, _, rest, hr, equal⟩ := (mem_productFirst I (ZFSet.prod T T) _).1 entry
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨u, hu, w, hw, rfl⟩ := ZFSet.mem_prod.1 hr
    exact ⟨ht, u, hu, w, hw, hz⟩
  · rintro ⟨ht, u, hu, w, hw, member⟩
    exact ⟨ht, stageOneAssignment t u w, member,
      (mem_productFirst I (ZFSet.prod T T) _).2
        ⟨t, ht, ZFSet.pair u w, ZFSet.pair_mem_prod.2 ⟨hu, hw⟩, rfl⟩⟩

theorem mem_assignmentOnIndices (B T A z : ZFSet.{u}) :
    z ∈ assignmentOnIndices B T A ↔ z ∈ A ∧ z ∈ stageOneAssignments B T :=
  ZFSet.mem_sep

theorem assignmentOnIndices_entry (B T A t u w : ZFSet.{u}) :
    stageOneAssignment t u w ∈ assignmentOnIndices B T A ↔
      stageOneAssignment t u w ∈ A ∧ t ∈ B ∧ u ∈ T ∧ w ∈ T := by
  rw [mem_assignmentOnIndices, stageOneAssignment_mem_assignments]

theorem assignmentIndices_on (I T B A : ZFSet.{u}) :
    assignmentIndices I T (assignmentOnIndices B T A) = assignmentIndices I T A ∩ B := by
  apply ZFSet.ext
  intro t
  rw [mem_assignmentIndices, ZFSet.mem_inter, mem_assignmentIndices]
  constructor
  · rintro ⟨ht, u, hu, w, hw, entry⟩
    have e := (assignmentOnIndices_entry B T A t u w).1 entry
    exact ⟨⟨ht, u, hu, w, hw, e.1⟩, e.2.1⟩
  · rintro ⟨⟨ht, u, hu, w, hw, entry⟩, hb⟩
    exact ⟨ht, u, hu, w, hw, (assignmentOnIndices_entry B T A t u w).2
      ⟨entry, hb, hu, hw⟩⟩

theorem assignment_subset_iff_indices_subset {I T A X : ZFSet.{u}}
    (subset : A ⊆ stageOneAssignments I T) :
    A ⊆ stageOneAssignments X T ↔ assignmentIndices I T A ⊆ X := by
  constructor
  · intro h t ht
    obtain ⟨_, u, _, w, _, entry⟩ := (mem_assignmentIndices I T A t).1 ht
    exact ((stageOneAssignment_mem_assignments X T t u w).1 (h entry)).1
  · intro h z hz
    obtain ⟨t, ht, u, hu, w, hw, rfl⟩ := (mem_stageOneAssignments I T z).1 (subset hz)
    exact (stageOneAssignment_mem_assignments X T t u w).2
      ⟨h ((mem_assignmentIndices I T A t).2 ⟨ht, u, hu, w, hw, hz⟩), hu, hw⟩





theorem mem_assignmentQueriesWithin (Q X T q : ZFSet.{u}) :
    q ∈ assignmentQueriesWithin Q X T ↔ q ∈ Q ∧ AssignmentQueryWithin X T q :=
  ZFSet.mem_sep

theorem representativeIndexStep_contains (I T Q c X : ZFSet.{u}) :
    X ⊆ representativeIndexStep I T Q c X :=
  fun _ member => ZFSet.mem_union.2 (Or.inl member)

theorem representativeIndexStep_subset {I T Q c X : ZFSet.{u}} (subset : X ⊆ I) :
    representativeIndexStep I T Q c X ⊆ I := by
  intro i member
  exact (ZFSet.mem_union.1 member).elim (fun h => subset h)
    (fun h => ((mem_representativeIndexAdditions I T Q c X i).1 h).1)

theorem representativeIndexStep_covers {I T Q c X q row A : ZFSet.{u}}
    (query : q ∈ Q) (within : AssignmentQueryWithin X T q)
    (entry : ZFSet.pair q (ZFSet.pair row A) ∈ c) :
    assignmentIndices I T A ⊆ representativeIndexStep I T Q c X := by
  intro i member
  obtain ⟨hi, v, hv, w, hw, e⟩ := (mem_assignmentIndices I T A i).1 member
  exact ZFSet.mem_union.2 (Or.inr
    ((mem_representativeIndexAdditions I T Q c X i).2
      ⟨hi, q, query, within, row, A, entry, v, hv, w, hw, e⟩))

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem assignmentIndices_mem {I T A : ZFSet.{u}}
    (hI : I ∈ M.sets) (hT : T ∈ M.sets) (hA : A ∈ M.sets) :
    assignmentIndices I T A ∈ M.sets :=
  M.relationImage_mem separation hA hI (M.productFirst_mem pairing unions powers separation
    hI (M.prod_mem pairing unions powers separation hT hT))

theorem assignmentOnIndices_mem {B T A : ZFSet.{u}}
    (hB : B ∈ M.sets) (hT : T ∈ M.sets) (hA : A ∈ M.sets) :
    assignmentOnIndices B T A ∈ M.sets :=
  M.bounded_separation_mem separation (.mem 0 1)
    (extend (stageOneAssignments B T) Fin.elim0)
    (Fin.cases (M.stageOneAssignments_mem pairing unions powers separation hB hT)
      (fun i => Fin.elim0 i)) hA

theorem assignmentIndices_small
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {I T A N : ZFSet.{u}} (hI : I ∈ M.sets) (hT : T ∈ M.sets)
    (hA : A ∈ M.sets) (hN : N ∈ M.sets) (small : M.groundEmbeddable A N) :
    M.groundEmbeddable (assignmentIndices I T A) N :=
  M.groundEmbeddable_function_image pairing unions powers separation choice hA hI hN
    (M.productFirst_mem pairing unions powers separation hI
      (M.prod_mem pairing unions powers separation hT hT)) (productFirst_function I (ZFSet.prod T T)) small

theorem assignmentOnIndices_small {B T A N : ZFSet.{u}}
    (hB : B ∈ M.sets) (hT : T ∈ M.sets) (hA : A ∈ M.sets)
    (hN : N ∈ M.sets) (small : M.groundEmbeddable A N) :
    M.groundEmbeddable (assignmentOnIndices B T A) N :=
  M.groundEmbeddable_restrict separation
    (M.assignmentOnIndices_mem pairing unions powers separation hB hT hA) hN
    (fun _ hz => (mem_assignmentOnIndices B T A _).1 hz |>.1) small

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
universe u

theorem stageOneRawTests_binary_union (M : TransitiveGround.{u}) (d : Fin 15 → ZFSet.{u})
    {A B lower : ZFSet.{u}} (agreement : AssignmentIndexAgreement A B)
    (first : stageOneRawTests M d A lower) (second : stageOneRawTests M d B lower) :
    stageOneRawTests M d (A ∪ B) lower := by
  refine ⟨?_, ?_⟩
  · intro t ht u hu w hw entry
    rcases ZFSet.mem_union.1 entry with entry | entry
    · exact first.1 t ht u hu w hw entry
    · exact second.1 t ht u hu w hw entry
  · intro t ht u hu u' hu' w hw w' hw' entry entry'
    rcases ZFSet.mem_union.1 entry with entry | entry
    · rcases ZFSet.mem_union.1 entry' with entry' | entry'
      · exact first.2 t ht u hu u' hu' w hw w' hw' entry entry'
      · exact first.2 t ht u hu u' hu' w hw w' hw' entry
          ((agreement t ⟨u, w, entry⟩ ⟨u', w', entry'⟩ u' w').2 entry')
    · rcases ZFSet.mem_union.1 entry' with entry' | entry'
      · exact second.2 t ht u hu u' hu' w hw w' hw' entry
          ((agreement t ⟨u', w', entry'⟩ ⟨u, w, entry⟩ u' w').1 entry')
      · exact second.2 t ht u hu u' hu' w hw w' hw' entry entry'





theorem assignment_representative_agreement {I T X A C : ZFSet.{u}}
    (first : A ⊆ stageOneAssignments I T) (second : C ⊆ stageOneAssignments I T)
    (contained : assignmentIndices I T C ⊆ X)
    (exactLists : assignmentOnIndices (assignmentIndices I T (assignmentOnIndices X T A)) T C =
      assignmentOnIndices X T A) : AssignmentIndexAgreement C A := by
  intro t atC atA
  obtain ⟨uC, wC, entryC⟩ := atC
  obtain ⟨uA, wA, entryA⟩ := atA
  have fieldsC := (stageOneAssignment_mem_assignments I T t uC wC).1 (second entryC)
  have fieldsA := (stageOneAssignment_mem_assignments I T t uA wA).1 (first entryA)
  have inX : t ∈ X := contained ((mem_assignmentIndices I T C t).2
    ⟨fieldsC.1, uC, fieldsC.2.1, wC, fieldsC.2.2, entryC⟩)
  have inQuery : t ∈ assignmentIndices I T (assignmentOnIndices X T A) := by
    rw [assignmentIndices_on, ZFSet.mem_inter]
    exact ⟨(mem_assignmentIndices I T A t).2
      ⟨fieldsA.1, uA, fieldsA.2.1, wA, fieldsA.2.2, entryA⟩, inX⟩
  intro u w
  constructor
  · intro entry
    have fields := (stageOneAssignment_mem_assignments I T t u w).1 (second entry)
    have selected := (assignmentOnIndices_entry _ T C t u w).2
      ⟨entry, inQuery, fields.2.1, fields.2.2⟩
    rw [exactLists] at selected
    exact ((assignmentOnIndices_entry X T A t u w).1 selected).1
  · intro entry
    have fields := (stageOneAssignment_mem_assignments I T t u w).1 (first entry)
    have selected := (assignmentOnIndices_entry X T A t u w).2
      ⟨entry, inX, fields.2.1, fields.2.2⟩
    rw [← exactLists] at selected
    exact ((assignmentOnIndices_entry _ T C t u w).1 selected).1

end PartitionPilot.Forcing




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_AssignmentQueryFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
universe u

theorem assignmentQueryRelation_entry (I T C D row L other A : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair row L) (ZFSet.pair other A) ∈ assignmentQueryRelation I T C D ↔
      ZFSet.pair row L ∈ C ∧ ZFSet.pair other A ∈ D ∧ row = other ∧
      assignmentOnIndices (assignmentIndices I T L) T A = L := by
  rw [assignmentQueryRelation, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hq, hp⟩, r, L', A', eq, matchList⟩
    obtain ⟨first, second⟩ := ZFSet.pair_inj.1 eq
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 first
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 second
    exact ⟨hq, hp, rfl, matchList⟩
  · rintro ⟨hq, hp, rfl, matchList⟩
    exact ⟨⟨hq, hp⟩, row, L, A, rfl, matchList⟩

theorem mem_realizedAssignmentQueries (I T C D q : ZFSet.{u}) :
    q ∈ realizedAssignmentQueries I T C D ↔
      q ∈ C ∧ ∃ p ∈ D, ZFSet.pair q p ∈ assignmentQueryRelation I T C D := by
  rw [realizedAssignmentQueries, mem_relationImage]
  constructor
  · rintro ⟨hq, p, hp, entry⟩
    exact ⟨hq, p, hp, ((pair_mem_relationConverse C D _ q p).1 entry).2.2⟩
  · rintro ⟨hq, p, hp, entry⟩
    exact ⟨hq, p, hp, (pair_mem_relationConverse C D _ q p).2 ⟨hq, hp, entry⟩⟩

theorem assignmentIndexOverlap_iff (I T L z : ZFSet.{u}) :
    (∃ i ∈ I, ∃ w ∈ L,
      ZFSet.pair z i ∈ productFirst I (ZFSet.prod T T) ∧
      ZFSet.pair w i ∈ productFirst I (ZFSet.prod T T)) ↔
    z ∈ stageOneAssignments (assignmentIndices I T L) T := by
  constructor
  · rintro ⟨i, hi, w, hw, first, second⟩
    obtain ⟨j, _, rest, hr, equal⟩ := (mem_productFirst I (ZFSet.prod T T) _).1 first
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ZFSet.pair_mem_prod.2
      ⟨(mem_relationImage L I _ _).2 ⟨hi, w, hw, second⟩, hr⟩
  · intro member
    obtain ⟨i, hi, rest, hr, rfl⟩ := ZFSet.mem_prod.1 member
    obtain ⟨hi, w, hw, second⟩ := (mem_relationImage L I _ i).1 hi
    exact ⟨i, hi, w, hw, (mem_productFirst I (ZFSet.prod T T) _).2
      ⟨i, hi, rest, hr, rfl⟩, second⟩

namespace BoundedFormula
open SetFormula

theorem truth_assignmentQueryOverlapFormula {n} (z I L f : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (assignmentQueryOverlapFormula z I L f) env ↔
      ∃ i ∈ env I, ∃ w ∈ env L,
        ZFSet.pair (env z) i ∈ env f ∧ ZFSet.pair w i ∈ env f := by
  simp only [assignmentQueryOverlapFormula, truth_exMem, Truth, truth_pairMembershipFormula]
  rfl

theorem truth_assignmentQueryMatchFormula {n} (I L A f : Fin n)
    (env : Fin n → ZFSet.{u}) (T : ZFSet.{u})
    (projection : env f = productFirst (env I) (ZFSet.prod T T)) :
    Truth (assignmentQueryMatchFormula I L A f) env ↔
      assignmentOnIndices (assignmentIndices (env I) T (env L)) T (env A) = env L := by
  simp only [assignmentQueryMatchFormula, Truth, truth_imp, truth_assignmentQueryOverlapFormula]
  change ((∀ z ∈ env L, z ∈ env A ∧ ∃ i ∈ env I, ∃ w ∈ env L,
    ZFSet.pair z i ∈ env f ∧ ZFSet.pair w i ∈ env f) ∧
    (∀ z ∈ env A, (∃ i ∈ env I, ∃ w ∈ env L,
    ZFSet.pair z i ∈ env f ∧ ZFSet.pair w i ∈ env f) → z ∈ env L)) ↔ _
  simp only [projection, assignmentIndexOverlap_iff]
  constructor
  · intro h
    apply ZFSet.ext
    intro z
    rw [mem_assignmentOnIndices]
    exact ⟨fun hz => h.2 z hz.1 hz.2, fun hz => h.1 z hz⟩
  · intro equal
    constructor
    · intro z hz
      exact (mem_assignmentOnIndices _ _ _ z).1 (equal.symm ▸ hz)
    · intro z hz hi
      exact equal ▸ (mem_assignmentOnIndices _ _ _ z).2 ⟨hz, hi⟩

theorem truth_assignmentQueryRelationFormula {n} (z I f : Fin n)
    (env : Fin n → ZFSet.{u}) (T : ZFSet.{u})
    (projection : env f = productFirst (env I) (ZFSet.prod T T)) :
    Truth (assignmentQueryRelationFormula z I f) env ↔
      ∃ row L A, env z = ZFSet.pair (ZFSet.pair row L) (ZFSet.pair row A) ∧
        assignmentOnIndices (assignmentIndices (env I) T L) T A = L := by
  simp only [assignmentQueryRelationFormula, truth_exPairFields]
  constructor
  · rintro ⟨q, p, hz, row, L, hq, other, A, hp, same, matchList⟩
    change q = ZFSet.pair row L at hq
    change p = ZFSet.pair other A at hp
    change row = other at same
    have eq := (truth_assignmentQueryMatchFormula I.succ.succ.succ.succ.succ.succ 2 0
      f.succ.succ.succ.succ.succ.succ
      (extend A (extend other (extend L (extend row (extend p (extend q env)))))) T projection).1 matchList
    exact ⟨row, L, A, by rw [hz, hq, hp, ← same], eq⟩
  · rintro ⟨row, L, A, hz, matchList⟩
    exact ⟨ZFSet.pair row L, ZFSet.pair row A, hz, row, L, rfl, row, A, rfl,
      rfl, (truth_assignmentQueryMatchFormula I.succ.succ.succ.succ.succ.succ 2 0
        f.succ.succ.succ.succ.succ.succ
        (extend A (extend row (extend L (extend row
          (extend (ZFSet.pair row A) (extend (ZFSet.pair row L) env)))))) T projection).2 matchList⟩

end BoundedFormula

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GreedyAntichainTraces
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
universe u

theorem OrderAntichainCode.eq_of_common_lower {Q order D p q : ZFSet.{u}}
    (antichain : OrderAntichainCode Q order D) (first : p ∈ D) (second : q ∈ D)
    (common : ∃ r ∈ Q, ZFSet.pair r p ∈ order ∧ ZFSet.pair r q ∈ order) : p = q := by
  obtain ⟨r, member, belowFirst, belowSecond⟩ := common
  exact antichain.2 p first q second r member belowFirst belowSecond

theorem mem_antichainEligible (Q order D alpha prior q : ZFSet.{u}) :
    q ∈ antichainEligible Q order D alpha prior ↔ q ∈ D ∧
      ¬ ∃ beta ∈ alpha, ∃ p ∈ D, ZFSet.pair beta p ∈ prior ∧
        ∃ r ∈ Q, ZFSet.pair r q ∈ order ∧ ZFSet.pair r p ∈ order :=
  ZFSet.mem_sep

theorem greedyAntichainStep_selected {Q order D F c alpha prior y : ZFSet.{u}}
    (choice : ChoiceFunctionCode F c)
    (step : GreedyAntichainStep Q order D F c alpha prior y) (selected : y ∈ D) :
    y ∈ antichainEligible Q order D alpha prior := by
  rcases step with ⟨E, _, rfl, entry⟩ | ⟨_, equal⟩
  · exact choice.chosen _ _ entry
  · exact False.elim (ZFSet.mem_irrefl D (equal ▸ selected))

theorem greedyAntichainStep_of_nonempty {Q order D F c alpha prior y : ZFSet.{u}}
    (choice : ChoiceFunctionCode F c)
    (step : GreedyAntichainStep Q order D F c alpha prior y)
    (nonempty : (antichainEligible Q order D alpha prior).Nonempty) :
    y ∈ antichainEligible Q order D alpha prior := by
  rcases step with ⟨E, _, rfl, entry⟩ | ⟨empty, _⟩
  · exact choice.chosen _ _ entry
  · exact False.elim (empty nonempty)

theorem greedyAntichainTrace_antichain {Q order D F c C f S : ZFSet.{u}}
    (choice : ChoiceFunctionCode F c) (ordinal : ordinalSetProperty C)
    (trace : OrdinalRecursionTrace (GreedyAntichainStep Q order D F c) C f)
    (conditions : D ⊆ Q) (subset : S ⊆ C) :
    OrderAntichainCode Q order (relationImage S D f) := by
  refine ⟨fun p hp => conditions ((mem_relationImage S D f p).1 hp).1, ?_⟩
  intro p hp q hq r hr rp rq
  obtain ⟨hpD, beta, hBeta, bp⟩ := (mem_relationImage S D f p).1 hp
  obtain ⟨hqD, gamma, hGamma, gq⟩ := (mem_relationImage S D f q).1 hq
  rcases ordinalSetProperty_mem_compare ordinal (subset hBeta) (subset hGamma) with
    before | equal | after
  · have eligible := greedyAntichainStep_selected choice
      (trace.2 gamma (subset hGamma) q gq) hqD
    exact False.elim ((mem_antichainEligible Q order D gamma
      (graphRestriction gamma f) q).1 eligible |>.2 <|
      ⟨beta, before, p, hpD, pair_mem_graphRestriction.2 ⟨bp, before⟩, r, hr, rq, rp⟩)
  · subst gamma
    exact trace.1.unique bp gq
  · have eligible := greedyAntichainStep_selected choice
      (trace.2 beta (subset hBeta) p bp) hpD
    exact False.elim ((mem_antichainEligible Q order D beta
      (graphRestriction beta f) p).1 eligible |>.2 <|
      ⟨gamma, after, q, hqD, pair_mem_graphRestriction.2 ⟨gq, after⟩, r, hr, rp, rq⟩)

theorem greedyAntichainTrace_injection {Q order D F c C f : ZFSet.{u}}
    (choice : ChoiceFunctionCode F c) (ordinal : ordinalSetProperty C)
    (trace : OrdinalRecursionTrace (GreedyAntichainStep Q order D F c) C f)
    (orderCode : PartialOrderCode Q order) (conditions : D ⊆ Q)
    (available : ∀ alpha ∈ C,
      (antichainEligible Q order D alpha (graphRestriction alpha f)).Nonempty) :
    InjectionCode C D f := by
  have fresh : ∀ alpha ∈ C, ∀ y, ZFSet.pair alpha y ∈ f →
      y ∈ D ∧ ¬ ∃ beta ∈ alpha, ZFSet.pair beta y ∈ f := by
    intro alpha hAlpha y entry
    obtain ⟨hyD, eligible⟩ := (mem_antichainEligible Q order D alpha
      (graphRestriction alpha f) y).1
      (greedyAntichainStep_of_nonempty choice (trace.2 alpha hAlpha y entry)
        (available alpha hAlpha))
    refine ⟨hyD, ?_⟩
    rintro ⟨beta, hBeta, byEntry⟩
    have refl := orderCode.refl y (conditions hyD)
    exact eligible ⟨beta, hBeta, y, hyD, pair_mem_graphRestriction.2 ⟨byEntry, hBeta⟩,
      y, conditions hyD, refl, refl⟩
  refine ⟨⟨?_, trace.1.to_isFunc.2⟩, ?_⟩
  · intro z hz
    obtain ⟨alpha, hAlpha, y, rfl⟩ := trace.1.shape z hz
    exact ZFSet.pair_mem_prod.2 ⟨hAlpha, (fresh alpha hAlpha y hz).1⟩
  · intro alpha beta y first second
    have hAlpha := trace.1.pair_source first
    have hBeta := trace.1.pair_source second
    rcases ordinalSetProperty_mem_compare ordinal hAlpha hBeta with before | equal | after
    · exact False.elim ((fresh beta hBeta y second).2 ⟨alpha, before, first⟩)
    · exact equal
    · exact False.elim ((fresh alpha hAlpha y first).2 ⟨beta, after, second⟩)

theorem greedyAntichainTrace_exhausts {Q order D F c C f : ZFSet.{u}}
    (choice : ChoiceFunctionCode F c) (ordinal : ordinalSetProperty C)
    (trace : OrdinalRecursionTrace (GreedyAntichainStep Q order D F c) C f)
    (orderCode : PartialOrderCode Q order) (conditions : D ⊆ Q)
    (impossible : ¬ InjectionCode C D f) :
    ∃ alpha ∈ C,
      ¬ (antichainEligible Q order D alpha (graphRestriction alpha f)).Nonempty := by
  classical
  by_contra none
  apply impossible
  exact greedyAntichainTrace_injection choice ordinal trace orderCode conditions
    (fun alpha hAlpha => by
      by_contra empty
      exact none ⟨alpha, hAlpha, empty⟩)

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GreedyAntichainStepFormulas
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

theorem truth_antichainBlockedFormula {n} (q Q order D alpha prior : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (antichainBlockedFormula q Q order D alpha prior) env ↔
      ∃ beta ∈ env alpha, ∃ p ∈ env D, ZFSet.pair beta p ∈ env prior ∧
        ∃ r ∈ env Q, ZFSet.pair r (env q) ∈ env order ∧ ZFSet.pair r p ∈ env order := by
  simp only [antichainBlockedFormula, truth_exMem, Truth, truth_pairMembershipFormula]
  rfl

theorem truth_antichainEligibleFormula {n} (E Q order D alpha prior : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (antichainEligibleFormula E Q order D alpha prior) env ↔
      env E = antichainEligible (env Q) (env order) (env D) (env alpha) (env prior) := by
  simp only [antichainEligibleFormula, Truth, truth_imp, truth_antichainBlockedFormula, ← iff_def]
  change ((∀ q ∈ env E, q ∈ env D) ∧ ∀ q ∈ env D,
    q ∈ env E ↔ ¬ ∃ beta ∈ env alpha, ∃ p ∈ env D,
      ZFSet.pair beta p ∈ env prior ∧ ∃ r ∈ env Q,
        ZFSet.pair r q ∈ env order ∧ ZFSet.pair r p ∈ env order) ↔ _
  constructor
  · rintro ⟨subset, spec⟩
    apply ZFSet.ext
    intro q
    rw [mem_antichainEligible]
    exact ⟨fun hq => ⟨subset q hq, (spec q (subset q hq)).1 hq⟩,
      fun ⟨hq, fresh⟩ => (spec q hq).2 fresh⟩
  · intro equal
    rw [equal]
    exact ⟨fun _ hq => (mem_antichainEligible _ _ _ _ _ _).1 hq |>.1,
      fun q hq => by rw [mem_antichainEligible]; exact and_iff_right hq⟩

theorem truth_greedyAntichainStepFormula {n} (Q order D F c alpha prior y : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (greedyAntichainStepFormula Q order D F c alpha prior y) env ↔
      GreedyAntichainStep (env Q) (env order) (env D) (env F) (env c)
        (env alpha) (env prior) (env y) := by
  simp only [greedyAntichainStepFormula, truth_disj, truth_exMem, Truth,
    truth_antichainEligibleFormula, truth_pairMembershipFormula, truth_antichainBlockedFormula]
  change ((∃ E ∈ env F, E = antichainEligible (env Q) (env order) (env D) (env alpha) (env prior) ∧
    ZFSet.pair E (env y) ∈ env c) ∨
    (¬ (∃ q ∈ env D, ¬ ∃ beta ∈ env alpha, ∃ p ∈ env D,
      ZFSet.pair beta p ∈ env prior ∧ ∃ r ∈ env Q,
        ZFSet.pair r q ∈ env order ∧ ZFSet.pair r p ∈ env order) ∧ env y = env D)) ↔ _
  have nonempty : (antichainEligible (env Q) (env order) (env D) (env alpha) (env prior)).Nonempty ↔
      ∃ q ∈ env D, ¬ ∃ beta ∈ env alpha, ∃ p ∈ env D,
        ZFSet.pair beta p ∈ env prior ∧ ∃ r ∈ env Q,
          ZFSet.pair r q ∈ env order ∧ ZFSet.pair r p ∈ env order := by
    change (∃ q, q ∈ antichainEligible (env Q) (env order) (env D) (env alpha) (env prior)) ↔ _
    simp only [mem_antichainEligible]
  simp only [GreedyAntichainStep, nonempty]

end PartitionPilot.Forcing.BoundedFormula

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_RefinementHistoryPrefixLevels
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})





theorem historyUnion_countable_capture
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {history B : ZFSet.{u}} (hh : history ∈ M.sets) (hB : B ∈ M.sets)
    (small : M.groundEmbeddable B ZFSet.omega)
    (subset : B ⊆ refinementHistoryIndices
      (M.groundOmegaOne pairing unions powers separation collection infinite) history) :
    ∃ beta ∈ M.groundOmegaOne pairing unions powers separation collection infinite,
      B ⊆ refinementHistoryIndices beta history := by
  let C := M.groundOmegaOne pairing unions powers separation collection infinite
  have hC := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
  let formula : SetFormula 3 := .ex (.conj (pairMembershipFormula 2 0 3) (.mem 1 0))
  let params : Fin 1 → ZFSet.{u} := ![history]
  have members : ∀ j, params j ∈ M.sets := Fin.cases hh (fun j => Fin.elim0 j)
  have recognize (x alpha : ZFSet.{u}) (ha : alpha ∈ M.sets) :
      Realize M.sets formula (extend x (extend alpha params)) ↔
        ∃ Y, ZFSet.pair alpha Y ∈ history ∧ x ∈ Y := by
    rw [show formula = .ex (.conj (pairMembershipFormula 2 0 3) (.mem 1 0)) from rfl, realize_ex]
    constructor
    · rintro ⟨Y, hY, entry, inside⟩
      exact ⟨Y, (M.realize_pairMembershipFormula pairing 2 0 3
        (extend Y (extend x (extend alpha params))) ha hY hh).1 entry, inside⟩
    · rintro ⟨Y, entry, inside⟩
      have hY := M.transitive (M.union_mem unions (M.union_mem unions hh))
        (pair_second_mem_doubleUnion entry)
      exact ⟨Y, hY, (M.realize_pairMembershipFormula pairing 2 0 3
        (extend Y (extend x (extend alpha params))) ha hY hh).2 entry, inside⟩
  let relation := M.definableRelation formula params B C
  have relationGround := M.definableRelation_mem pairing unions powers separation formula params members hB hC
  have total : ∀ x ∈ B, ∃ alpha ∈ C, ZFSet.pair x alpha ∈ relation := by
    intro x hx
    obtain ⟨alpha, ha, Y, entry, inside⟩ := (mem_refinementHistoryIndices C history x).1 (subset hx)
    exact ⟨alpha, ha, (M.pair_mem_definableRelation formula params B C x alpha).2
      ⟨hx, ha, (recognize x alpha (M.transitive hC ha)).2 ⟨Y, entry, inside⟩⟩⟩
  obtain ⟨selection, ground, function, selected⟩ :=
    M.uniformize_relation pairing unions powers separation choice hB hC relationGround total
  have rangeGround := M.relationImage_mem separation hB hC ground
  have rangeSmall := M.groundEmbeddable_function_image pairing unions powers separation choice
    hB hC (M.omega_mem separation infinite) ground function small
  obtain ⟨beta, hBeta, bounds⟩ := M.groundOmegaOne_countable_bound
    pairing unions powers separation collection infinite choice rangeGround
    (fun _ h => ((mem_relationImage B C selection _).1 h).1) rangeSmall
  refine ⟨beta, hBeta, ?_⟩
  intro x hx
  obtain ⟨alpha, entry, _⟩ := function.2 x hx
  have ha := (ZFSet.pair_mem_prod.1 (function.1 entry)).2
  obtain ⟨Y, stored, inside⟩ := (recognize x alpha (M.transitive hC ha)).1
    ((M.pair_mem_definableRelation formula params B C x alpha).1 (selected entry)).2.2
  exact (mem_refinementHistoryIndices beta history x).2
    ⟨alpha, bounds alpha ((mem_relationImage B C selection alpha).2 ⟨ha, x, hx, entry⟩), Y, stored, inside⟩

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundHistoryUnionBounds
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing.GroundInaccessibleConditions
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}
variable (conditions : GroundInaccessibleConditions M K)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hK : K ∈ M.sets)
include conditions pairing unions powers separation hK

include infinite choice in
theorem binary_union {A B : ZFSet.{u}}
    (first : A ∈ M.sets ∧ GroundBelow M A K) (second : B ∈ M.sets ∧ GroundBelow M B K) :
    A ∪ B ∈ M.sets ∧ GroundBelow M (A ∪ B) K :=
  ⟨M.binary_union_mem pairing unions first.1 second.1,
    GroundBelow.binary_union pairing unions powers separation infinite choice first.1 second.1 hK
      conditions.2.1 conditions.1 conditions.2.2.1 conditions.2.2.2 first.2 second.2⟩

end PartitionPilot.Forcing.GroundInaccessibleConditions

namespace PartitionPilot.Forcing.GroundInaccessibleConditions
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}
variable (conditions : GroundInaccessibleConditions M K)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hK : K ∈ M.sets)
include conditions pairing unions powers separation infinite choice hK

theorem finite_family_union (n : Nat) (family : Fin n → ZFSet.{u})
    (small : ∀ i, family i ∈ M.sets ∧ GroundBelow M (family i) K) :
    ∃ U, U ∈ M.sets ∧ GroundBelow M U K ∧
      ∀ x, x ∈ U ↔ ∃ i, x ∈ family i := by
  induction n with
  | zero =>
    refine ⟨∅, M.empty_mem ⟨K, hK⟩,
      (GroundBelow.empty_iff hK).2 ⟨ZFSet.omega, conditions.2.1⟩, ?_⟩
    intro x
    constructor
    · intro h
      exact False.elim (ZFSet.notMem_empty x h)
    · rintro ⟨i, _⟩
      exact Fin.elim0 i
  | succ n ih =>
    obtain ⟨U, hU, smallU, members⟩ := ih (fun i => family i.succ) (fun i => small i.succ)
    have whole := conditions.binary_union pairing unions powers separation infinite choice hK
      (small 0) ⟨hU, smallU⟩
    refine ⟨family 0 ∪ U, whole.1, whole.2, ?_⟩
    intro x
    rw [ZFSet.mem_union, members]
    constructor
    · rintro (first | ⟨i, later⟩)
      · exact ⟨0, first⟩
      · exact ⟨i.succ, later⟩
    · rintro ⟨i, member⟩
      exact Fin.cases (fun h => Or.inl h)
        (fun j h => Or.inr ⟨j, h⟩) i member

end PartitionPilot.Forcing.GroundInaccessibleConditions

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (separation : SeparationSchema M.sets)
variable {n : Nat} {f : (Fin (n + 1) → ZFSet.{u}) → ZFSet.{u}}

include pairing unions separation in
theorem exists_historyUnionTrace (collection : CollectionSchema M.sets)
    (defined : GroundDefinableFunction M f) (params : Fin n → ZFSet.{u})
    (members : ∀ j, params j ∈ M.sets)
    {stages : ZFSet.{u}} (hs : stages ∈ M.sets) (ordinal : ordinalSetProperty stages) :
    ∃ history ∈ M.sets, OrdinalRecursionTrace
      (fun alpha prior output => output = f (extend (refinementHistoryIndices alpha prior) params))
      stages history := by
  let operation := M.historyUnionStepDefinition pairing unions separation defined
  let slots : Fin (n + 3) → Fin (n + 3) :=
    Fin.cases 2 (Fin.cases 0 (Fin.cases 1 (fun j => j.succ.succ.succ)))
  let formula := SetFormula.reindex slots operation.formula
  have recognize (alpha prior output : ZFSet.{u}) (ha : alpha ∈ M.sets)
      (hp : prior ∈ M.sets) (ho : output ∈ M.sets) :
      Realize M.sets formula (extend alpha (extend prior (extend output params))) ↔
        output = f (extend (refinementHistoryIndices alpha prior) params) := by
    rw [show formula = SetFormula.reindex slots operation.formula from rfl, realize_reindex]
    have eqEnv : (fun i => extend alpha (extend prior (extend output params)) (slots i)) =
        extend output (extend alpha (extend prior params)) := by
      funext i
      exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.cases rfl (fun _ => rfl) k) j) i
    rw [eqEnv]
    exact operation.correct (extend alpha (extend prior params))
      (Fin.cases ha (Fin.cases hp members)) output ho
  have closure : GroundOrdinalStepClosure M stages formula params := by
    intro alpha member prior hp _
    have ha := M.transitive hs member
    have outputGround := operation.closed (extend alpha (extend prior params))
      (Fin.cases ha (Fin.cases hp members))
    refine ⟨_, outputGround, (recognize alpha prior _ ha hp outputGround).2 rfl, ?_⟩
    intro z hz relation
    exact (recognize alpha prior z ha hp hz).1 relation
  obtain ⟨history, hh, trace⟩ := M.exists_ordinalRecursionTrace pairing unions separation collection
    hs ordinal formula params members closure
  refine ⟨history, hh, trace.1, ?_⟩
  intro alpha member output entry
  have step := trace.2 alpha member output entry
  exact (recognize alpha _ output (M.transitive hs member) step.1 step.2.1).1 step.2.2

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable {I K : ZFSet.{u}} (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
variable (phi : ZFSet.{u} → ZFSet.{u})
variable (preserves : ∀ X ∈ M.sets, X ⊆ I → GroundBelow M X K →
  phi X ⊆ I ∧ GroundBelow M (phi X) K)
include pairing unions powers separation choice hK conditions preserves

theorem historyUnionTrace_below :
    ∀ stages ∈ K, ∀ history ∈ M.sets,
      OrdinalRecursionTrace (fun alpha prior output => output = phi (refinementHistoryIndices alpha prior))
        stages history →
      (∀ alpha Y, ZFSet.pair alpha Y ∈ history → Y ⊆ I ∧ GroundBelow M Y K) ∧
      refinementHistoryIndices stages history ⊆ I ∧
      GroundBelow M (refinementHistoryIndices stages history) K := by
  intro stages
  induction stages using ZFSet.inductionOn with
  | h stages ih =>
    intro hStages history hh trace
    have hs := M.transitive hK hStages
    have ordinal := ordinalSetProperty_member conditions.1 hStages
    have fibers : ∀ alpha Y, ZFSet.pair alpha Y ∈ history → Y ⊆ I ∧ GroundBelow M Y K := by
      intro alpha Y entry
      have member := trace.1.pair_source entry
      have ha := M.transitive hs member
      have lower := ih alpha member (conditions.1.1 stages hStages alpha member)
        (graphRestriction alpha history) (M.graphRestriction_mem unions separation ha hh)
        (trace.restrict (ordinalSetProperty_member ordinal member) (ordinal.1 alpha member))
      have earlierGround := M.refinementHistoryIndices_mem unions separation ha
        (M.graphRestriction_mem unions separation ha hh)
      have result := preserves _ earlierGround lower.2.1 lower.2.2
      exact (trace.2 alpha member Y entry).symm ▸ result
    refine ⟨fibers, ?_, ?_⟩
    · intro x hx
      obtain ⟨alpha, _, Y, entry, inside⟩ := (mem_refinementHistoryIndices stages history x).1 hx
      exact (fibers alpha Y entry).1 inside
    · exact GroundBelow.indexed_sUnion pairing unions powers separation choice hs
        (M.union_mem unions (M.union_mem unions hh)) hh hK conditions.1
        conditions.2.2.1 conditions.2.2.2 (GroundBelow.of_member pairing unions powers separation hK hStages)
        trace.1.to_isFunc (fun alpha Y entry => (fibers alpha Y entry).2)

end PartitionPilot.Forcing.TransitiveGround

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

theorem truth_orderAntichainFormula {n} (Q order A : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (orderAntichainFormula Q order A) env ↔ OrderAntichainCode (env Q) (env order) (env A) := by
  simp only [orderAntichainFormula, Truth, truth_imp, truth_pairMembershipFormula]
  constructor
  · rintro ⟨subset, law⟩
    exact ⟨subset, fun p hp q hq r hr first second => law p hp q hq r hr ⟨first, second⟩⟩
  · rintro ⟨subset, law⟩
    exact ⟨subset, fun p hp q hq r hr both => law p hp q hq r hr both.1 both.2⟩

theorem truth_relativeMaximalAntichainFormula {n} (Q order D A : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (relativeMaximalAntichainFormula Q order D A) env ↔
      RelativeMaximalAntichainCode (env Q) (env order) (env D) (env A) := by
  simp only [relativeMaximalAntichainFormula, Truth, truth_orderAntichainFormula,
    truth_exMem, truth_pairMembershipFormula]
  rfl





theorem truth_relativeAntichainFamilyFormula {n} (j A Q order domains : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (relativeAntichainFamilyFormula j A Q order domains) env ↔
      ∃ D, ZFSet.pair (env j) D ∈ env domains ∧
        RelativeMaximalAntichainCode (env Q) (env order) D (env A) := by
  simp only [relativeAntichainFamilyFormula, truth_exGraphFields, Truth,
    truth_relativeMaximalAntichainFormula]
  change (∃ key D, ZFSet.pair key D ∈ env domains ∧ key = env j ∧
    RelativeMaximalAntichainCode (env Q) (env order) D (env A)) ↔ _
  constructor
  · rintro ⟨key, D, entry, rfl, code⟩
    exact ⟨D, entry, code⟩
  · rintro ⟨D, entry, code⟩
    exact ⟨env j, D, entry, rfl, code⟩





end PartitionPilot.Forcing.BoundedFormula

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundInvariantNamePowers
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

theorem orderedPairNameFamily_below
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {one X Y K : ZFSet.{u}}
    (hone : one ∈ M.sets) (hX : X ∈ M.sets) (hY : Y ∈ M.sets) (hK : K ∈ M.sets)
    (standard : GroundStandardInaccessible M K)
    (smallX : GroundBelow M X K) (smallY : GroundBelow M Y K) :
    GroundBelow M (orderedPairNameFamily one X Y) K := by
  obtain ⟨ordinal, omega, regular, strong⟩ := standard.to_conditions pairing unions powers separation hK
  have hSingleton : ({one} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hone hone
  have singletonSmall := GroundBelow.singleton pairing unions powers separation infinite hK omega hone
  have hUnion := M.binary_union_mem pairing unions hX hY
  have unionSmall := GroundBelow.binary_union pairing unions powers separation infinite choice
    hX hY hK omega ordinal regular strong smallX smallY
  have hFirst := M.prod_mem pairing unions powers separation hUnion hSingleton
  have firstSmall := GroundBelow.product pairing unions powers separation hUnion hSingleton hK
    ordinal strong unionSmall singletonSmall
  have hPower := M.groundPower_mem powers hFirst
  have powerSmall := strong.power_closed pairing unions powers separation hFirst hK firstSmall
  have hSecond := M.prod_mem pairing unions powers separation hPower hSingleton
  have secondSmall := GroundBelow.product pairing unions powers separation hPower hSingleton hK
    ordinal strong powerSmall singletonSmall
  have boundSmall := strong.power_closed pairing unions powers separation hSecond hK secondSmall
  exact boundSmall.restrict separation
    (M.orderedPairNameFamily_mem pairing unions powers separation hone hX hY) hK
    (M.orderedPairNameFamily_subset_bound pairing hone hX hY)

theorem iteratedPairNameFamily_below
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {one T K : ZFSet.{u}}
    (hone : one ∈ M.sets) (hT : T ∈ M.sets) (hK : K ∈ M.sets)
    (standard : GroundStandardInaccessible M K) (small : GroundBelow M T K) (n : Nat) :
    GroundBelow M (iteratedPairNameFamily one T n) K := by
  induction n with
  | zero => exact small
  | succ n ih =>
      exact M.orderedPairNameFamily_below pairing unions powers separation infinite choice hone
        (M.iteratedPairNameFamily_mem pairing unions powers separation hone hT n) hT hK standard ih small

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



namespace PartitionPilot.Forcing.RecursiveRefinementOrderHistory
universe u
variable {M : TransitiveGround.{u}} {rows rowOrder T stages history : ZFSet.{u}}
variable (run : RecursiveRefinementOrderHistory M rows rowOrder T stages history)
variable {row A B : ZFSet.{u}}
local notation "levels" => refinementDataHistoryLevels stages history T
include run

theorem binary_union_mem_of_candidates (ordinal : ordinalSetProperty stages)
    (mono : ∀ beta (d : Fin 15 → ZFSet.{u}),
      ZFSet.pair beta (refinementFormulaDataCode d) ∈ history →
      ∀ C lower stronger, stageOneRawTests M d C lower →
        ZFSet.pair stronger lower ∈ d 8 → stageOneRawTests M d C stronger)
    (first : ZFSet.pair row A ∈ M.refinementHistoryForcing rows T stages history)
    (second : ZFSet.pair row B ∈ M.refinementHistoryForcing rows T stages history)
    (rowSelf : ZFSet.pair row row ∈ rowOrder) (agreement : AssignmentIndexAgreement A B)
    (candidate : ZFSet.pair row (A ∪ B) ∈
      M.stageOneCandidateBound rows (refinementDataHistoryIndices stages history) T)
    (candidates : ∀ gamma ∈ stages, ZFSet.pair row (assignmentCut levels gamma (A ∪ B)) ∈
      M.stageOneCandidateBound rows
        (refinementDataHistoryIndices gamma (graphRestriction gamma history)) T) :
    ZFSet.pair row (A ∪ B) ∈ M.refinementHistoryForcing rows T stages history := by
  have subsetA : A ⊆ A ∪ B := fun _ h => ZFSet.mem_union.2 (Or.inl h)
  have subsetB : B ⊆ A ∪ B := fun _ h => ZFSet.mem_union.2 (Or.inr h)
  have firstTests := ((M.mem_refinementHistoryForcing rows T stages history _).1 first).2
  have secondTests := ((M.mem_refinementHistoryForcing rows T stages history _).1 second).2
  have step (beta : ZFSet.{u}) (hbeta : beta ∈ stages) (d : Fin 15 → ZFSet.{u})
      (entry : ZFSet.pair beta (refinementFormulaDataCode d) ∈ history)
      (proved : ZFSet.pair row (assignmentCut levels beta (A ∪ B)) ∈
        M.refinementHistoryForcing rows T beta (graphRestriction beta history)) :
      stageOneRawTests M d (A ∪ B) (ZFSet.pair row (assignmentCut levels beta (A ∪ B))) := by
    have storedA := (forcingHistoryConditionCode_lookup_iff run.carriers.data.function).1 firstTests
      beta hbeta (refinementFormulaDataCode d) entry
    have checkedA := (stageTwoConditionCode_pair_iff M d _ beta row A).1
      ((packedSuccessorConditionCode_code_iff M _ beta d _).1 storedA)
    have storedB := (forcingHistoryConditionCode_lookup_iff run.carriers.data.function).1 secondTests
      beta hbeta (refinementFormulaDataCode d) entry
    have checkedB := (stageTwoConditionCode_pair_iff M d _ beta row B).1
      ((packedSuccessorConditionCode_code_iff M _ beta d _).1 storedB)
    have belowA : ZFSet.pair (ZFSet.pair row (assignmentCut levels beta (A ∪ B)))
        (ZFSet.pair row (assignmentCut levels beta A)) ∈ d 8 := by
      rw [run.order beta d entry]
      exact (M.pair_mem_refinementHistoryOrder rows rowOrder T beta (graphRestriction beta history)
        _ _ _ _).2 ⟨proved, run.carriers.cut_mem first hbeta, rowSelf, assignmentCut_mono subsetA⟩
    have belowB : ZFSet.pair (ZFSet.pair row (assignmentCut levels beta (A ∪ B)))
        (ZFSet.pair row (assignmentCut levels beta B)) ∈ d 8 := by
      rw [run.order beta d entry]
      exact (M.pair_mem_refinementHistoryOrder rows rowOrder T beta (graphRestriction beta history)
        _ _ _ _).2 ⟨proved, run.carriers.cut_mem second hbeta, rowSelf, assignmentCut_mono subsetB⟩
    exact stageOneRawTests_binary_union M d agreement
      (mono beta d entry A _ _ checkedA.2 belowA) (mono beta d entry B _ _ checkedB.2 belowB)
  have earlier : ∀ gamma ∈ stages, ZFSet.pair row (assignmentCut levels gamma (A ∪ B)) ∈
      M.refinementHistoryForcing rows T gamma (graphRestriction gamma history) := by
    intro gamma
    induction gamma using ZFSet.inductionOn with
    | h gamma ih =>
      intro hgamma
      apply (M.mem_refinementHistoryForcing rows T gamma (graphRestriction gamma history) _).2
      refine ⟨candidates gamma hgamma, ?_⟩
      intro beta hbeta
      have betaFull := ordinal.1 gamma hgamma beta hbeta
      have betaSubset := ordinal.2 gamma hgamma beta hbeta
      obtain ⟨data, entry⟩ := run.carriers.data.function.total betaFull
      obtain ⟨d, rfl⟩ := run.carriers.data.decoded beta data entry
      have proved := ih beta hbeta betaFull
      have sameCut := run.carriers.data.prefix_cut (ordinal.1 gamma hgamma) betaSubset
        (assignmentCut levels gamma (A ∪ B))
      refine ⟨refinementFormulaDataCode d, pair_mem_graphRestriction.2 ⟨entry, hbeta⟩, ?_⟩
      apply (packedSuccessorConditionCode_code_iff M _ beta d _).2
      apply (stageTwoConditionCode_pair_iff M d _ beta row _).2
      rw [sameCut, assignmentCut_nested betaSubset]
      refine ⟨(run.carriers.carrier beta d entry).symm ▸ proved, ?_⟩
      exact stageOneRawTests_transfer M d _ (step beta betaFull d entry proved)
        (fun _ _ _ _ _ _ member => assignmentCut_subset levels gamma (A ∪ B) member)
  apply (M.mem_refinementHistoryForcing rows T stages history _).2
  refine ⟨candidate, ?_⟩
  intro beta hbeta
  obtain ⟨data, entry⟩ := run.carriers.data.function.total hbeta
  obtain ⟨d, rfl⟩ := run.carriers.data.decoded beta data entry
  refine ⟨refinementFormulaDataCode d, entry, ?_⟩
  apply (packedSuccessorConditionCode_code_iff M _ beta d _).2
  apply (stageTwoConditionCode_pair_iff M d _ beta row _).2
  exact ⟨(run.carriers.carrier beta d entry).symm ▸ earlier beta hbeta,
    step beta hbeta d entry (earlier beta hbeta)⟩

end PartitionPilot.Forcing.RecursiveRefinementOrderHistory



namespace PartitionPilot.Forcing.RecursiveRefinementOrderHistory
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {rows rowOrder T stages history : ZFSet.{u}}
variable (run : RecursiveRefinementOrderHistory M rows rowOrder T stages history)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets) (hT : T ∈ M.sets)
include run pairing unions powers separation infinite choice hStages hHistory hT

theorem binary_union_extension (ordinal : ordinalSetProperty stages)
    (mono : ∀ beta (d : Fin 15 → ZFSet.{u}),
      ZFSet.pair beta (refinementFormulaDataCode d) ∈ history →
      ∀ C lower stronger, stageOneRawTests M d C lower →
        ZFSet.pair stronger lower ∈ d 8 → stageOneRawTests M d C stronger)
    (rowOrderLaw : PartialOrderCode rows rowOrder) {row A B : ZFSet.{u}}
    (first : ZFSet.pair row A ∈ M.refinementHistoryForcing rows T stages history)
    (second : ZFSet.pair row B ∈ M.refinementHistoryForcing rows T stages history)
    (agreement : AssignmentIndexAgreement A B) :
    ZFSet.pair row (A ∪ B) ∈ M.refinementHistoryForcing rows T stages history ∧
      ZFSet.pair (ZFSet.pair row (A ∪ B)) (ZFSet.pair row A) ∈
        M.refinementHistoryOrder rows rowOrder T stages history ∧
      ZFSet.pair (ZFSet.pair row (A ∪ B)) (ZFSet.pair row B) ∈
        M.refinementHistoryOrder rows rowOrder T stages history := by
  have firstCandidate := ((M.mem_refinementHistoryForcing rows T stages history _).1 first).1
  have secondCandidate := ((M.mem_refinementHistoryForcing rows T stages history _).1 second).1
  obtain ⟨hrow, hA, subsetA, smallA⟩ := (M.pair_mem_stageOneCandidateBound _ _ _ _ _).1 firstCandidate
  obtain ⟨_, hB, subsetB, smallB⟩ := (M.pair_mem_stageOneCandidateBound _ _ _ _ _).1 secondCandidate
  have rowSelf := rowOrderLaw.refl row hrow
  have candidate : ZFSet.pair row (A ∪ B) ∈
      M.stageOneCandidateBound rows (refinementDataHistoryIndices stages history) T := by
    apply (M.pair_mem_stageOneCandidateBound _ _ _ _ _).2
    refine ⟨hrow, M.binary_union_mem pairing unions hA hB, ?_,
      M.groundCountable_binary_union pairing unions powers separation infinite choice hA hB smallA smallB⟩
    intro z member
    exact (ZFSet.mem_union.1 member).elim (fun h => subsetA h) (fun h => subsetB h)
  have hLevels := M.refinementDataHistoryLevels_mem pairing unions powers separation hStages hHistory hT
  have member := run.binary_union_mem_of_candidates ordinal mono first second rowSelf agreement candidate
    (fun beta hbeta => M.refinementDataHistoryCandidate_cut separation run.carriers.data
      (ordinal.1 beta hbeta) hLevels (M.transitive hStages hbeta) (M.omega_mem separation infinite) candidate)
  refine ⟨member, ?_, ?_⟩
  · exact (M.pair_mem_refinementHistoryOrder rows rowOrder T stages history _ _ _ _).2
      ⟨member, first, rowSelf, fun _ h => ZFSet.mem_union.2 (Or.inl h)⟩
  · exact (M.pair_mem_refinementHistoryOrder rows rowOrder T stages history _ _ _ _).2
      ⟨member, second, rowSelf, fun _ h => ZFSet.mem_union.2 (Or.inr h)⟩

end PartitionPilot.Forcing.RecursiveRefinementOrderHistory

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundSmallAssignmentCuts
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

theorem small_assignmentCuts_bounded
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {U J K levels : ZFSet.{u}} (hU : U ∈ M.sets) (hK : K ∈ M.sets)
    (hLevels : levels ∈ M.sets) (regular : GroundRegular M K)
    (small : GroundBelow M U K) (function : ZFSet.IsFunc J K levels) (subset : U ⊆ J) :
    ∃ beta ∈ K, ∀ A, A ⊆ U → assignmentCut levels beta A = A := by
  have restricted : ZFSet.IsFunc U K (graphRestriction U levels) := by
    refine ⟨?_, ?_⟩
    · intro z member
      obtain ⟨x, hx, y, rfl, entry⟩ := mem_graphRestriction.1 member
      exact ZFSet.pair_mem_prod.2 ⟨hx, (ZFSet.pair_mem_prod.1 (function.1 entry)).2⟩
    · intro x hx
      obtain ⟨y, entry, unique⟩ := function.2 x (subset hx)
      exact ⟨y, pair_mem_graphRestriction.2 ⟨entry, hx⟩,
        fun z hz => unique z (pair_mem_graphRestriction.1 hz).1⟩
  obtain ⟨beta, hBeta, bound⟩ := regular.bound_small_domain pairing unions powers separation
    hU hK (M.graphRestriction_mem unions separation hU hLevels) small restricted
  refine ⟨beta, hBeta, fun A contained => assignmentCut_eq_of_lower ?_⟩
  intro z hz
  obtain ⟨level, entry, _⟩ := function.2 z (subset (contained hz))
  exact ⟨level, bound z level (pair_mem_graphRestriction.2 ⟨entry, contained hz⟩), entry⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundStructuralForcingHistoryConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem small_refinementConditionFamily_prefix
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {rows T K history D : ZFSet.{u}} (hRows : rows ∈ M.sets) (hT : T ∈ M.sets)
    (hK : K ∈ M.sets) (hHistory : history ∈ M.sets) (hD : D ∈ M.sets)
    (ordinal : ordinalSetProperty K) (omega : ZFSet.omega ∈ K)
    (regular : GroundRegular M K) (strong : GroundStrongLimit M K)
    (run : RecursiveRefinementDataHistory M rows T K history)
    (small : GroundBelow M D K) (members : D ⊆ M.refinementHistoryForcing rows T K history) :
    ∃ beta ∈ K, ∀ row A, ZFSet.pair row A ∈ D →
      assignmentCut (refinementDataHistoryLevels K history T) beta A = A ∧
      ZFSet.pair row A ∈ M.refinementHistoryForcing rows T beta (graphRestriction beta history) := by
  let J := stageOneAssignments (refinementDataHistoryIndices K history) T
  let S := M.groundSmallSubsets J ZFSet.omega
  let projection := productSecond rows S
  let R := relationImage D S projection
  let U := ⋃₀ R
  have hJ : J ∈ M.sets := M.stageOneAssignments_mem pairing unions powers separation
    (M.refinementDataHistoryIndices_mem pairing unions powers separation hK hHistory) hT
  have hS : S ∈ M.sets := M.groundSmallSubsets_mem powers separation hJ (M.transitive hK omega)
  have hProjection : projection ∈ M.sets := M.productSecond_mem pairing unions powers separation hRows hS
  have hR : R ∈ M.sets := M.relationImage_mem separation hD hS hProjection
  have hU : U ∈ M.sets := M.union_mem unions hR
  have smallR : GroundBelow M R K := small.function_image pairing unions powers separation choice
    hD hS hK hProjection (productSecond_function rows S)
  have smallU : GroundBelow M U K := GroundBelow.sUnion pairing unions powers separation choice
    hR hK ordinal regular strong smallR (fun A hA =>
      GroundBelow.of_countable omega ((M.mem_groundSmallSubsets J ZFSet.omega A).1
        ((mem_relationImage D S projection A).1 hA).1).2.2)
  have subset : U ⊆ J := by
    intro z hz
    obtain ⟨A, hA, hz⟩ := ZFSet.mem_sUnion.1 hz
    have inS := ((mem_relationImage D S projection A).1 hA).1
    exact ((M.mem_groundSmallSubsets J ZFSet.omega A).1 inS).2.1 hz
  obtain ⟨beta, hBeta, cuts⟩ := M.small_assignmentCuts_bounded pairing unions powers separation
    hU hK (M.refinementDataHistoryLevels_mem pairing unions powers separation hK hHistory hT)
    regular smallU run.data.levels_function subset
  refine ⟨beta, hBeta, ?_⟩
  intro row A member
  have actual := members member
  have candidate := ((M.mem_refinementHistoryForcing rows T K history _).1 actual).1
  have pair : row ∈ rows ∧ A ∈ S := ZFSet.pair_mem_prod.1 candidate
  have inR : A ∈ R := (mem_relationImage D S projection A).2 ⟨pair.2, ZFSet.pair row A,
    member, (mem_productSecond rows S _).2 ⟨row, pair.1, A, pair.2, rfl⟩⟩
  have cut := cuts A (fun z hz => ZFSet.mem_sUnion.2 ⟨A, inR, hz⟩)
  exact ⟨cut, cut ▸ run.cut_mem actual hBeta⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem structuralForcingTrace_small_family_prefix
    (rows rowOrder rowTop rowAction G nodes nodeOrder nodeAction basis T T2 : ZFSet.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hRows : rows ∈ M.sets) (hG : G ∈ M.sets) (hNodes : nodes ∈ M.sets)
    (hNodeOrder : nodeOrder ∈ M.sets) (hBasis : basis ∈ M.sets)
    (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
    {K history : ZFSet.{u}} (hK : K ∈ M.sets) (hHistory : history ∈ M.sets)
    (conditions : GroundInaccessibleConditions M K)
    (trace : OrdinalRecursionTrace
      (fun level prior stage => stage = M.structuralForcingStage rows rowOrder rowTop rowAction
        G nodes nodeOrder nodeAction basis T T2 level prior) K history) :
    let packed := M.structuralRefinementHistory G nodes nodeOrder basis T T2 K history
    ∀ D ∈ M.sets, GroundBelow M D K → D ⊆ M.refinementHistoryForcing rows T K packed →
      ∃ beta ∈ K, ∀ row A, ZFSet.pair row A ∈ D →
        assignmentCut (refinementDataHistoryLevels K packed T) beta A = A ∧
        ZFSet.pair row A ∈ M.refinementHistoryForcing rows T beta (graphRestriction beta packed) := by
  dsimp only
  intro D hD small members
  have packed := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![G, nodes, nodeOrder, basis, T, T2, K, history]
    (Fin.cases hG (Fin.cases hNodes (Fin.cases hNodeOrder (Fin.cases hBasis
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hK (Fin.cases hHistory (fun j => Fin.elim0 j)))))))))
  have run := M.structuralForcingTrace_recursiveOrder rows rowOrder rowTop rowAction G nodes
    nodeOrder nodeAction basis T T2 conditions.1 trace
  exact M.small_refinementConditionFamily_prefix pairing unions powers separation choice hRows hT hK
    packed hD conditions.1 conditions.2.1 conditions.2.2.1 conditions.2.2.2 run.carriers small members





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

theorem semanticStructuralTrace_binary_union_extension
    {stages history : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (ordinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
    (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0) :
    let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 stages history
    ∀ row A B : ZFSet.{u},
      ZFSet.pair row A ∈ M.refinementHistoryForcing c.carrier T stages packed →
      ZFSet.pair row B ∈ M.refinementHistoryForcing c.carrier T stages packed →
      AssignmentIndexAgreement A B →
      ZFSet.pair row (A ∪ B) ∈ M.refinementHistoryForcing c.carrier T stages packed ∧
        ZFSet.pair (ZFSet.pair row (A ∪ B)) (ZFSet.pair row A) ∈
          M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed ∧
        ZFSet.pair (ZFSet.pair row (A ∪ B)) (ZFSet.pair row B) ∈
          M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed := by
  dsimp only
  intro row A B first second agreement
  have run := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix)
    T T2 ordinal trace
  have witnesses := M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace
  have mono := M.structuralHistory_rawTests_mono t b d base directed T T2 stages history
    pairing unions powers separation collection group nodes supports hh hT witnesses
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  exact run.binary_union_extension pairing unions powers separation infinite choice hs hPacked hT
    ordinal mono c.conditionOrder_code first second agreement

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundOrdinaryMembershipAntichainFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem antichainEligible_mem (separation : SeparationSchema M.sets)
    {Q order D alpha prior : ZFSet.{u}} (hQ : Q ∈ M.sets) (hOrder : order ∈ M.sets)
    (hD : D ∈ M.sets) (hAlpha : alpha ∈ M.sets) (hPrior : prior ∈ M.sets) :
    antichainEligible Q order D alpha prior ∈ M.sets := by
  let formula : BoundedFormula 6 := .neg (BoundedFormula.antichainBlockedFormula 0 1 2 3 4 5)
  let params := extend Q (extend order (extend D (extend alpha (extend prior Fin.elim0))))
  have ground := M.bounded_separation_mem separation formula params
    (Fin.cases hQ (Fin.cases hOrder (Fin.cases hD
      (Fin.cases hAlpha (Fin.cases hPrior (fun i => Fin.elim0 i)))))) hD
  have equal : ZFSet.sep (fun q => BoundedFormula.Truth formula (extend q params)) D =
      antichainEligible Q order D alpha prior := by
    apply ZFSet.ext
    intro q
    simp only [ZFSet.mem_sep, antichainEligible, formula, BoundedFormula.Truth,
      BoundedFormula.truth_antichainBlockedFormula]
    rfl
  exact equal ▸ ground

theorem greedyAntichainStep_exists_unique (separation : SeparationSchema M.sets)
    {Q order D c alpha prior : ZFSet.{u}} (hQ : Q ∈ M.sets) (hOrder : order ∈ M.sets)
    (hD : D ∈ M.sets) (hAlpha : alpha ∈ M.sets) (hPrior : prior ∈ M.sets)
    (code : ChoiceFunctionCode (M.nonemptyGroundSubsets D) c) :
    ∃ y ∈ M.sets, GreedyAntichainStep Q order D (M.nonemptyGroundSubsets D) c alpha prior y ∧
      ∀ z, GreedyAntichainStep Q order D (M.nonemptyGroundSubsets D) c alpha prior z → z = y := by
  classical
  let E := antichainEligible Q order D alpha prior
  have hE := M.antichainEligible_mem separation hQ hOrder hD hAlpha hPrior
  have subset : E ⊆ D := fun _ hq => (mem_antichainEligible _ _ _ _ _ _).1 hq |>.1
  by_cases nonempty : E.Nonempty
  · have member := (M.mem_nonemptyGroundSubsets D E).2 ⟨hE, subset, nonempty⟩
    obtain ⟨y, entry, unique⟩ := code.function.2 E member
    have hy := code.chosen E y entry
    refine ⟨y, M.transitive hD (subset hy), Or.inl ⟨E, member, rfl, entry⟩, ?_⟩
    intro z step
    rcases step with ⟨S, _, rfl, selected⟩ | ⟨empty, _⟩
    · exact unique z selected
    · exact False.elim (empty nonempty)
  · refine ⟨D, hD, Or.inr ⟨nonempty, rfl⟩, ?_⟩
    intro z step
    rcases step with ⟨S, member, rfl, _⟩ | ⟨_, equal⟩
    · exact False.elim (nonempty ((M.mem_nonemptyGroundSubsets D _).1 member).2.2)
    · exact equal

theorem exists_greedyAntichainTrace
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    {Q order D c C : ZFSet.{u}} (hQ : Q ∈ M.sets) (hOrder : order ∈ M.sets)
    (hD : D ∈ M.sets) (hc : c ∈ M.sets) (hC : C ∈ M.sets)
    (ordinal : ordinalSetProperty C)
    (code : ChoiceFunctionCode (M.nonemptyGroundSubsets D) c) :
    ∃ history ∈ M.sets, OrdinalRecursionTrace
      (GreedyAntichainStep Q order D (M.nonemptyGroundSubsets D) c) C history := by
  let F := M.nonemptyGroundSubsets D
  have hF : F ∈ M.sets := M.nonemptyGroundSubsets_mem powers separation hD
  let params := extend Q (extend order (extend D (extend F (extend c Fin.elim0))))
  have members : ∀ i, params i ∈ M.sets :=
    Fin.cases hQ (Fin.cases hOrder (Fin.cases hD
      (Fin.cases hF (Fin.cases hc (fun i => Fin.elim0 i)))))
  let formula : BoundedFormula 8 := BoundedFormula.greedyAntichainStepFormula 3 4 5 6 7 0 1 2
  have recognize (alpha prior y : ZFSet.{u}) (hAlpha : alpha ∈ M.sets)
      (hPrior : prior ∈ M.sets) (hy : y ∈ M.sets) :
      Realize M.sets formula.toFormula (extend alpha (extend prior (extend y params))) ↔
        GreedyAntichainStep Q order D F c alpha prior y :=
    (BoundedFormula.realize_toFormula M formula _
      (Fin.cases hAlpha (Fin.cases hPrior (Fin.cases hy members)))).trans
      (BoundedFormula.truth_greedyAntichainStepFormula 3 4 5 6 7 0 1 2 _)
  have closure : GroundOrdinalStepClosure M C formula.toFormula params := by
    intro alpha member prior hPrior _
    have hAlpha := M.transitive hC member
    obtain ⟨y, hy, step, unique⟩ :=
      M.greedyAntichainStep_exists_unique separation hQ hOrder hD hAlpha hPrior code
    exact ⟨y, hy, (recognize alpha prior y hAlpha hPrior hy).2 step,
      fun z hz relation => unique z ((recognize alpha prior z hAlpha hPrior hz).1 relation)⟩
  obtain ⟨history, hHistory, trace⟩ := M.exists_ordinalRecursionTrace pairing unions separation collection
    hC ordinal formula.toFormula params members closure
  refine ⟨history, hHistory, trace.1, ?_⟩
  intro alpha member y entry
  have step := trace.2 alpha member y entry
  exact (recognize alpha _ y (M.transitive hC member) step.1 step.2.1).1 step.2.2

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem greedyAntichainTrace_relativeMaximal {Q order D F c C f alpha : ZFSet.{u}}
    (choice : ChoiceFunctionCode F c) (ordinal : ordinalSetProperty C)
    (trace : OrdinalRecursionTrace (GreedyAntichainStep Q order D F c) C f)
    (conditions : D ⊆ Q) (hAlpha : alpha ∈ C)
    (exhausted : ¬ (antichainEligible Q order D alpha (graphRestriction alpha f)).Nonempty) :
    RelativeMaximalAntichainCode Q order D (relationImage alpha D f) := by
  classical
  refine ⟨fun p hp => ((mem_relationImage alpha D f p).1 hp).1,
    greedyAntichainTrace_antichain choice ordinal trace conditions
      (fun beta hBeta => ordinal.1 alpha hAlpha beta hBeta), ?_⟩
  intro q hq
  by_contra missing
  apply exhausted
  refine ⟨q, (mem_antichainEligible Q order D alpha (graphRestriction alpha f) q).2
    ⟨hq, ?_⟩⟩
  rintro ⟨beta, hBeta, p, hp, entry, r, hr, rq, rp⟩
  exact missing ⟨p, (mem_relationImage alpha D f p).2
    ⟨hp, beta, hBeta, (pair_mem_graphRestriction.1 entry).1⟩, r, hr, rq, rp⟩

theorem RelativeMaximalAntichainCode.predense {Q order D A : ZFSet.{u}}
    (code : RelativeMaximalAntichainCode Q order D A)
    (orderCode : PartialOrderCode Q order) (conditions : D ⊆ Q)
    (dense : ∀ q ∈ Q, ∃ d ∈ D, ZFSet.pair d q ∈ order) :
    ∀ q ∈ Q, ∃ p ∈ A, ∃ r ∈ Q,
      ZFSet.pair r q ∈ order ∧ ZFSet.pair r p ∈ order := by
  intro q hq
  obtain ⟨d, hd, dq⟩ := dense q hq
  obtain ⟨p, hp, r, hr, rd, rp⟩ := code.2.2 d hd
  exact ⟨p, hp, r, hr, orderCode.trans r hr d (conditions hd) q hq rd dq, rp⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem exists_groundRelativeMaximalAntichain
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {Q order D : ZFSet.{u}} (hQ : Q ∈ M.sets) (hOrder : order ∈ M.sets) (hD : D ∈ M.sets)
    (orderCode : PartialOrderCode Q order) (conditions : D ⊆ Q) :
    ∃ A ∈ M.sets, RelativeMaximalAntichainCode Q order D A := by
  let F := M.nonemptyGroundSubsets D
  have hF := M.nonemptyGroundSubsets_mem powers separation hD
  obtain ⟨c, hc, chooser⟩ := M.choice_witness choice hF
    (fun E hE => ((M.mem_nonemptyGroundSubsets D E).1 hE).2.2)
  obtain ⟨C, hC, ordinal, _, impossible⟩ := M.exists_groundHartogs
    pairing unions powers separation collection hD
  obtain ⟨f, hf, trace⟩ := M.exists_greedyAntichainTrace
    pairing unions powers separation collection hQ hOrder hD hc hC ordinal chooser
  obtain ⟨alpha, hAlpha, exhausted⟩ := greedyAntichainTrace_exhausts chooser ordinal trace
    orderCode conditions (fun injection => impossible ⟨f, hf, injection⟩)
  exact ⟨relationImage alpha D f,
    M.relationImage_mem separation (M.transitive hC hAlpha) hD hf,
    greedyAntichainTrace_relativeMaximal chooser ordinal trace conditions hAlpha exhausted⟩

end TransitiveGround

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem ordinaryMembershipDecisions_mem (separation : SeparationSchema M.sets)
    {Q order sigma tau : ZFSet.{u}} (hQ : Q ∈ M.sets) (hOrder : order ∈ M.sets)
    (hSigma : sigma ∈ M.sets) (hTau : tau ∈ M.sets) :
    M.ordinaryMembershipDecisions Q order sigma tau ∈ M.sets :=
  (M.definable_ordinaryMembershipDecisions separation).closed ![sigma, Q, order, tau]
    (Fin.cases hSigma (Fin.cases hQ (Fin.cases hOrder (Fin.cases hTau (fun i => Fin.elim0 i)))))

theorem pair_mem_ordinaryMembershipDecisionFamily (T Q order tau sigma D : ZFSet.{u}) :
    ZFSet.pair sigma D ∈ M.ordinaryMembershipDecisionFamily T Q order tau ↔
      sigma ∈ T ∧ D = M.ordinaryMembershipDecisions Q order sigma tau := by
  rw [ordinaryMembershipDecisionFamily, mem_familyCodeGraph]
  constructor
  · rintro ⟨x, equal⟩
    obtain ⟨hx, hd⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hx ▸ x.property, hd.symm.trans (congrArg (fun y => M.ordinaryMembershipDecisions Q order y tau) hx)⟩
  · rintro ⟨member, rfl⟩
    exact ⟨⟨sigma, member⟩, rfl⟩

theorem ordinaryMembershipDecisionFamily_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    {T Q order tau : ZFSet.{u}} (hT : T ∈ M.sets) (hQ : Q ∈ M.sets)
    (hOrder : order ∈ M.sets) (hTau : tau ∈ M.sets) :
    M.ordinaryMembershipDecisionFamily T Q order tau ∈ M.sets :=
  (M.definable_ordinaryMembershipDecisions separation).graph_mem pairing separation collection
    ![Q, order, tau] (Fin.cases hQ (Fin.cases hOrder (Fin.cases hTau (fun i => Fin.elim0 i)))) hT

theorem ordinaryMembershipDecisionFamily_function
    (separation : SeparationSchema M.sets)
    {T Q order tau : ZFSet.{u}} (hT : T ∈ M.sets) (hQ : Q ∈ M.sets)
    (hOrder : order ∈ M.sets) (hTau : tau ∈ M.sets) :
    ZFSet.IsFunc T (M.groundPower Q) (M.ordinaryMembershipDecisionFamily T Q order tau) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨sigma, rfl⟩ := (mem_familyCodeGraph _ _ z).1 hz
    exact ZFSet.pair_mem_prod.2 ⟨sigma.property, (M.mem_groundPower Q _).2
      ⟨M.ordinaryMembershipDecisions_mem separation hQ hOrder (M.transitive hT sigma.property) hTau,
        M.ordinaryMembershipDecisions_subset Q order sigma.val tau⟩⟩
  · intro sigma hSigma
    exact ⟨M.ordinaryMembershipDecisions Q order sigma tau,
      (M.pair_mem_ordinaryMembershipDecisionFamily T Q order tau sigma _).2 ⟨hSigma, rfl⟩,
      fun D entry => (M.pair_mem_ordinaryMembershipDecisionFamily T Q order tau sigma D).1 entry |>.2⟩

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem ordinaryMembershipDecisionFamily_dense
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ sigma ∈ T, IsName s sigma)
    (tau : (M.nameDomain s).names) :
    ∀ sigma D, ZFSet.pair sigma D ∈
      M.ordinaryMembershipDecisionFamily T s.carrier s.conditionOrder tau.val.val →
      ∀ p ∈ s.carrier, ∃ q ∈ D, ZFSet.pair q p ∈ s.conditionOrder := by
  intro sigma D entry
  obtain ⟨member, rfl⟩ := (M.pair_mem_ordinaryMembershipDecisionFamily
    T s.carrier s.conditionOrder tau.val.val sigma D).1 entry
  let name : (M.nameDomain s).names := ⟨⟨sigma, valid sigma member⟩, M.transitive hT member⟩
  exact M.ordinaryMembershipDecisions_dense s pairing unions powers separation collection carrier order name tau

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem exists_relativeMaximalAntichainFamily
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {Q order J domains : ZFSet.{u}} (hQ : Q ∈ M.sets) (hOrder : order ∈ M.sets)
    (hJ : J ∈ M.sets) (hDomains : domains ∈ M.sets)
    (orderCode : PartialOrderCode Q order)
    (domainsCode : ZFSet.IsFunc J (M.groundPower Q) domains) :
    ∃ f ∈ M.sets, ZFSet.IsFunc J (M.groundPower Q) f ∧
      ∀ j D A, ZFSet.pair j D ∈ domains → ZFSet.pair j A ∈ f →
        RelativeMaximalAntichainCode Q order D A := by
  let B := M.groundPower Q
  let formula : SetFormula 5 := (BoundedFormula.relativeAntichainFamilyFormula 0 1 2 3 4).toFormula
  let params := extend Q (extend order (extend domains Fin.elim0))
  have members : ∀ i, params i ∈ M.sets :=
    Fin.cases hQ (Fin.cases hOrder (Fin.cases hDomains (fun i => Fin.elim0 i)))
  have recognize (j A : ZFSet.{u}) (hj : j ∈ M.sets) (hA : A ∈ M.sets) :
      Realize M.sets formula (extend j (extend A params)) ↔
        ∃ D, ZFSet.pair j D ∈ domains ∧ RelativeMaximalAntichainCode Q order D A :=
    (BoundedFormula.realize_toFormula M _ _ (Fin.cases hj (Fin.cases hA members))).trans
      (BoundedFormula.truth_relativeAntichainFamilyFormula 0 1 2 3 4 _)
  have hB : B ∈ M.sets := M.groundPower_mem powers hQ
  let relation := M.definableRelation formula params J B
  have ground : relation ∈ M.sets := M.definableRelation_mem
    pairing unions powers separation formula params members hJ hB
  have total : ∀ j ∈ J, ∃ A ∈ B, ZFSet.pair j A ∈ relation := by
    intro j hj
    obtain ⟨D, entry, _⟩ := domainsCode.2 j hj
    have domain := (M.mem_groundPower Q D).1 (ZFSet.pair_mem_prod.1 (domainsCode.1 entry)).2
    obtain ⟨A, hA, code⟩ := M.exists_groundRelativeMaximalAntichain
      pairing unions powers separation collection choice hQ hOrder domain.1 orderCode domain.2
    have inB : A ∈ B := (M.mem_groundPower Q A).2 ⟨hA, code.2.1.1⟩
    exact ⟨A, inB, (M.pair_mem_definableRelation formula params J B j A).2
      ⟨hj, inB, (recognize j A (M.transitive hJ hj) hA).2 ⟨D, entry, code⟩⟩⟩
  obtain ⟨f, hf, function, selected⟩ := M.uniformize_relation
    pairing unions powers separation choice hJ hB ground total
  refine ⟨f, hf, function, ?_⟩
  intro j D A domainEntry chosen
  obtain ⟨hj, hA, holds⟩ := (M.pair_mem_definableRelation formula params J B j A).1 (selected chosen)
  obtain ⟨D', entry, code⟩ := (recognize j A (M.transitive hJ hj)
    ((M.mem_groundPower Q A).1 hA).1).1 holds
  obtain ⟨value, _, unique⟩ := domainsCode.2 j hj
  have equal : D' = D := (unique D' entry).trans (unique D domainEntry).symm
  exact equal ▸ code

theorem exists_smallRelativeAntichainFamily
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {Q order J domains K : ZFSet.{u}} (hQ : Q ∈ M.sets) (hOrder : order ∈ M.sets)
    (hJ : J ∈ M.sets) (hDomains : domains ∈ M.sets) (hK : K ∈ M.sets)
    (conditions : GroundInaccessibleConditions M K) (orderCode : PartialOrderCode Q order)
    (domainsCode : ZFSet.IsFunc J (M.groundPower Q) domains)
    (smallJ : GroundBelow M J K)
    (chain : ∀ A ∈ M.sets, OrderAntichainCode Q order A → GroundBelow M A K) :
    ∃ f ∈ M.sets, ZFSet.IsFunc J (M.groundPower Q) f ∧
      (∀ j D A, ZFSet.pair j D ∈ domains → ZFSet.pair j A ∈ f →
        RelativeMaximalAntichainCode Q order D A) ∧
      let U := ⋃₀ relationImage J (M.groundPower Q) f
      U ∈ M.sets ∧ GroundBelow M U K ∧ U ⊆ Q := by
  obtain ⟨f, hf, function, selected⟩ := M.exists_relativeMaximalAntichainFamily
    pairing unions powers separation collection choice hQ hOrder hJ hDomains orderCode domainsCode
  have hPower := M.groundPower_mem powers hQ
  have small : ∀ j A, ZFSet.pair j A ∈ f → GroundBelow M A K := by
    intro j A entry
    have pair := ZFSet.pair_mem_prod.1 (function.1 entry)
    obtain ⟨D, domainEntry, _⟩ := domainsCode.2 j pair.1
    exact chain A ((M.mem_groundPower Q A).1 pair.2).1
      (selected j D A domainEntry entry).2.1
  refine ⟨f, hf, function, selected,
    M.union_mem unions (M.relationImage_mem separation hJ hPower hf),
    GroundBelow.indexed_sUnion pairing unions powers separation choice hJ hPower hf hK
      conditions.1 conditions.2.2.1 conditions.2.2.2 smallJ function small, ?_⟩
  intro q member
  obtain ⟨A, inRange, inA⟩ := ZFSet.mem_sUnion.1 member
  have inPower := ((mem_relationImage J (M.groundPower Q) f A).1 inRange).1
  exact ((M.mem_groundPower Q A).1 inPower).2 inA

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] (s : Presentation P)

theorem exists_ordinaryMembershipAntichainFamily
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {T K : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ sigma ∈ T, IsName s sigma)
    (tau : (M.nameDomain s).names) (hK : K ∈ M.sets)
    (conditions : GroundInaccessibleConditions M K) (smallT : GroundBelow M T K)
    (chain : ∀ A ∈ M.sets, OrderAntichainCode s.carrier s.conditionOrder A → GroundBelow M A K) :
    ∃ f ∈ M.sets, ZFSet.IsFunc T (M.groundPower s.carrier) f ∧
      (∀ sigma A, ZFSet.pair sigma A ∈ f →
        RelativeMaximalAntichainCode s.carrier s.conditionOrder
          (M.ordinaryMembershipDecisions s.carrier s.conditionOrder sigma tau.val.val) A ∧
        ∀ q ∈ s.carrier, ∃ p ∈ A, ∃ r ∈ s.carrier,
          ZFSet.pair r q ∈ s.conditionOrder ∧ ZFSet.pair r p ∈ s.conditionOrder) ∧
      let U := ⋃₀ relationImage T (M.groundPower s.carrier) f
      U ∈ M.sets ∧ GroundBelow M U K ∧ U ⊆ s.carrier := by
  let domains := M.ordinaryMembershipDecisionFamily T s.carrier s.conditionOrder tau.val.val
  have hDomains : domains ∈ M.sets := M.ordinaryMembershipDecisionFamily_mem
    pairing separation collection hT carrier order tau.property
  have domainsCode : ZFSet.IsFunc T (M.groundPower s.carrier) domains :=
    M.ordinaryMembershipDecisionFamily_function separation hT carrier order tau.property
  obtain ⟨f, hf, function, selected, whole⟩ := M.exists_smallRelativeAntichainFamily
    pairing unions powers separation collection choice carrier order hT hDomains hK conditions
    s.conditionOrder_code domainsCode smallT chain
  refine ⟨f, hf, function, ?_, whole⟩
  intro sigma A entry
  have hSigma := (ZFSet.pair_mem_prod.1 (function.1 entry)).1
  have domainEntry : ZFSet.pair sigma
      (M.ordinaryMembershipDecisions s.carrier s.conditionOrder sigma tau.val.val) ∈ domains :=
    (M.pair_mem_ordinaryMembershipDecisionFamily T s.carrier s.conditionOrder tau.val.val sigma _).2
      ⟨hSigma, rfl⟩
  have code := selected sigma _ A domainEntry entry
  exact ⟨code, code.predense s.conditionOrder_code
    (M.ordinaryMembershipDecisions_subset s.carrier s.conditionOrder sigma tau.val.val)
    (M.ordinaryMembershipDecisionFamily_dense s pairing unions powers separation collection carrier order
      hT valid tau sigma _ domainEntry)⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundRepresentativeIndexSteps
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

theorem assignmentQueriesWithin_mem (separation : SeparationSchema M.sets)
    {Q X T : ZFSet.{u}} (hQ : Q ∈ M.sets) (hX : X ∈ M.sets) (hT : T ∈ M.sets) :
    assignmentQueriesWithin Q X T ∈ M.sets := by
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.assignmentQueryWithinFormula 1 2 0) (extend X (extend T Fin.elim0))
    (Fin.cases hX (Fin.cases hT (fun i => Fin.elim0 i))) hQ
  simpa only [BoundedFormula.truth_assignmentQueryWithinFormula, assignmentQueriesWithin, extend,
    show (1 : Fin 3) = Fin.succ 0 from rfl,
    show (2 : Fin 3) = Fin.succ (Fin.succ 0) from rfl, Fin.cases_zero, Fin.cases_succ] using selected

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundStructuralFullIndexSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.GroundBelow
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {A B N K : ZFSet.{u}}
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem smallSubsets (hB : B ∈ M.sets) (hN : N ∈ M.sets) (hK : K ∈ M.sets)
    (strong : GroundStrongLimit M K) (small : GroundBelow M B K) :
    GroundBelow M (M.groundSmallSubsets B N) K :=
  (strong.power_closed pairing unions powers separation hB hK small).restrict
    separation (M.groundSmallSubsets_mem powers separation hB hN) hK
    (fun _ member => (ZFSet.mem_sep.1 member).1)

end PartitionPilot.Forcing.GroundBelow

namespace PartitionPilot.Forcing.GroundBelow
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {rows I T stages history K : ZFSet.{u}}
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem stageOneAssignments (hI : I ∈ M.sets) (hT : T ∈ M.sets) (hK : K ∈ M.sets)
    (ordinal : ordinalSetProperty K) (strong : GroundStrongLimit M K)
    (indices : GroundBelow M I K) (terms : GroundBelow M T K) :
    GroundBelow M (PartitionPilot.Forcing.stageOneAssignments I T) K :=
  product pairing unions powers separation hI
    (M.prod_mem pairing unions powers separation hT hT) hK ordinal strong indices
    (product pairing unions powers separation hT hT hK ordinal strong terms terms)

theorem stageOneCandidateBound (hRows : rows ∈ M.sets) (hI : I ∈ M.sets)
    (hT : T ∈ M.sets) (hK : K ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
    (ordinal : ordinalSetProperty K) (strong : GroundStrongLimit M K)
    (rowSize : GroundBelow M rows K) (indices : GroundBelow M I K)
    (terms : GroundBelow M T K) : GroundBelow M (M.stageOneCandidateBound rows I T) K :=
  product pairing unions powers separation hRows
    (M.groundSmallSubsets_mem powers separation
      (M.stageOneAssignments_mem pairing unions powers separation hI hT) omega)
    hK ordinal strong rowSize
    (smallSubsets pairing unions powers separation
      (M.stageOneAssignments_mem pairing unions powers separation hI hT) omega hK strong
      (stageOneAssignments pairing unions powers separation hI hT hK ordinal strong indices terms))

end PartitionPilot.Forcing.GroundBelow

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

open scoped ZFSet

theorem representativeIndexStep_below
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {rows I T Q c D X K : ZFSet.{u}}
    (hRows : rows ∈ M.sets) (hI : I ∈ M.sets) (hT : T ∈ M.sets)
    (hQ : Q ∈ M.sets) (hc : c ∈ M.sets) (hD : D ∈ M.sets) (hX : X ∈ M.sets)
    (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    (selector : ZFSet.IsFunc Q D c)
    (queries : Q ⊆ M.stageOneCandidateBound rows I T)
    (selected : D ⊆ M.stageOneCandidateBound rows I T)
    (smallRows : GroundBelow M rows K) (smallT : GroundBelow M T K)
    (smallX : GroundBelow M X K) :
    GroundBelow M (representativeIndexStep I T Q c X) K := by
  let QX := assignmentQueriesWithin Q X T
  let E := relationImage QX D c
  let J := stageOneAssignments I T
  let S := M.groundSmallSubsets J ZFSet.omega
  let projection := productSecond rows S
  let R := relationImage E S projection
  let U := ⋃₀ R
  have omega := M.omega_mem separation infinite
  have hQX : QX ∈ M.sets := M.assignmentQueriesWithin_mem separation hQ hX hT
  have queryBound : QX ⊆ M.stageOneCandidateBound rows X T := by
    intro q member
    obtain ⟨hq, row, L, rfl, inside⟩ := (mem_assignmentQueriesWithin Q X T q).1 member
    obtain ⟨hr, hL, _, countable⟩ := (M.pair_mem_stageOneCandidateBound rows I T row L).1 (queries hq)
    exact (M.pair_mem_stageOneCandidateBound rows X T row L).2 ⟨hr, hL, inside, countable⟩
  have smallQX : GroundBelow M QX K :=
    (GroundBelow.stageOneCandidateBound pairing unions powers separation hRows hX hT hK omega
      conditions.1 conditions.2.2.2 smallRows smallX smallT).restrict separation hQX hK queryBound
  have hE : E ∈ M.sets := M.relationImage_mem separation hQX hD hc
  have smallE : GroundBelow M E K := smallQX.function_image pairing unions powers separation choice
    hQX hD hK hc selector
  have hJ : J ∈ M.sets := M.stageOneAssignments_mem pairing unions powers separation hI hT
  have hS : S ∈ M.sets := M.groundSmallSubsets_mem powers separation hJ omega
  have hProjection : projection ∈ M.sets := M.productSecond_mem pairing unions powers separation hRows hS
  have hR : R ∈ M.sets := M.relationImage_mem separation hE hS hProjection
  have hU : U ∈ M.sets := M.union_mem unions hR
  have smallR : GroundBelow M R K := smallE.function_image pairing unions powers separation choice
    hE hS hK hProjection (productSecond_function rows S)
  have smallU : GroundBelow M U K := GroundBelow.sUnion pairing unions powers separation choice
    hR hK conditions.1 conditions.2.2.1 conditions.2.2.2 smallR (fun A member =>
      GroundBelow.of_countable conditions.2.1 ((M.mem_groundSmallSubsets J ZFSet.omega A).1
        ((mem_relationImage E S projection A).1 member).1).2.2)
  have smallIndices : GroundBelow M (assignmentIndices I T U) K :=
    smallU.function_image pairing unions powers separation choice hU hI hK
      (M.productFirst_mem pairing unions powers separation hI
        (M.prod_mem pairing unions powers separation hT hT)) (productFirst_function I (ZFSet.prod T T))
  have additionsGround := M.representativeIndexAdditions_mem separation hI hT hQ hc hX
  have additionsSubset : representativeIndexAdditions I T Q c X ⊆ assignmentIndices I T U := by
    intro i member
    obtain ⟨hi, q, hq, within, row, A, entry, v, hv, w, hw, inside⟩ :=
      (mem_representativeIndexAdditions I T Q c X i).1 member
    have inD := (ZFSet.pair_mem_prod.1 (selector.1 entry)).2
    have candidate := selected inD
    have pair : row ∈ rows ∧ A ∈ S := ZFSet.pair_mem_prod.1 candidate
    have inE : ZFSet.pair row A ∈ E := (mem_relationImage QX D c _).2
      ⟨inD, q, (mem_assignmentQueriesWithin Q X T q).2 ⟨hq, within⟩, entry⟩
    have inR : A ∈ R := (mem_relationImage E S projection A).2
      ⟨pair.2, ZFSet.pair row A, inE,
        (mem_productSecond rows S _).2 ⟨row, pair.1, A, pair.2, rfl⟩⟩
    exact (mem_assignmentIndices I T U i).2
      ⟨hi, v, hv, w, hw, ZFSet.mem_sUnion.2 ⟨A, inR, inside⟩⟩
  exact GroundBelow.binary_union pairing unions powers separation infinite choice hX additionsGround hK
    conditions.2.1 conditions.1 conditions.2.2.1 conditions.2.2.2 smallX
    (smallIndices.restrict separation additionsGround hK additionsSubset)

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRepresentativeAntichainBounds
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
variable {rows I T Q order D X : ZFSet.{u}}

theorem representative_antichain_subset_candidate
    (shape : Q ⊆ M.stageOneCandidateBound rows I T)
    (antichain : OrderAntichainCode Q order D)
    (compatible : ∀ row A C, ZFSet.pair row A ∈ Q → ZFSet.pair row C ∈ Q →
      AssignmentIndexAgreement A C →
      ∃ z ∈ Q, ZFSet.pair z (ZFSet.pair row A) ∈ order ∧
        ZFSet.pair z (ZFSet.pair row C) ∈ order)
    (representatives : ∀ row A, ZFSet.pair row A ∈ D →
      ∃ C, ZFSet.pair row C ∈ D ∧ assignmentIndices I T C ⊆ X ∧
        assignmentOnIndices (assignmentIndices I T (assignmentOnIndices X T A)) T C =
          assignmentOnIndices X T A) :
    D ⊆ M.stageOneCandidateBound rows X T := by
  intro q member
  obtain ⟨row, hRow, A, hA, subsetA, smallA, rfl⟩ :=
    (M.mem_stageOneCandidateBound rows I T q).1 (shape (antichain.1 member))
  obtain ⟨C, inD, contained, exactLists⟩ := representatives row A member
  have dataC := (M.pair_mem_stageOneCandidateBound rows I T row C).1 (shape (antichain.1 inD))
  have agreement := assignment_representative_agreement subsetA dataC.2.2.1 contained exactLists
  have equal := antichain.eq_of_common_lower inD member
    (compatible row C A (antichain.1 inD) (antichain.1 member) agreement)
  have same : C = A := (ZFSet.pair_inj.1 equal).2
  have subsetC := (assignment_subset_iff_indices_subset dataC.2.2.1).2 contained
  exact (M.pair_mem_stageOneCandidateBound rows X T row A).2
    ⟨hRow, hA, same ▸ subsetC, smallA⟩

theorem representative_antichain_below
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {K : ZFSet.{u}} (hRows : rows ∈ M.sets) (hX : X ∈ M.sets)
    (hT : T ∈ M.sets) (hK : K ∈ M.sets) (hD : D ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) (ordinal : ordinalSetProperty K)
    (strong : GroundStrongLimit M K)
    (smallRows : GroundBelow M rows K) (smallX : GroundBelow M X K)
    (smallT : GroundBelow M T K)
    (shape : Q ⊆ M.stageOneCandidateBound rows I T)
    (antichain : OrderAntichainCode Q order D)
    (compatible : ∀ row A C, ZFSet.pair row A ∈ Q → ZFSet.pair row C ∈ Q →
      AssignmentIndexAgreement A C →
      ∃ z ∈ Q, ZFSet.pair z (ZFSet.pair row A) ∈ order ∧
        ZFSet.pair z (ZFSet.pair row C) ∈ order)
    (representatives : ∀ row A, ZFSet.pair row A ∈ D →
      ∃ C, ZFSet.pair row C ∈ D ∧ assignmentIndices I T C ⊆ X ∧
        assignmentOnIndices (assignmentIndices I T (assignmentOnIndices X T A)) T C =
          assignmentOnIndices X T A) : GroundBelow M D K :=
  (GroundBelow.stageOneCandidateBound pairing unions powers separation hRows hX hT hK omega
    ordinal strong smallRows smallX smallT).restrict separation hD hK
    (M.representative_antichain_subset_candidate shape antichain compatible representatives)

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundAssignmentRepresentativeClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
universe u

theorem assignmentOnIndices_indices_on {I T X A : ZFSet.{u}}
    (shape : A ⊆ stageOneAssignments I T) :
    assignmentOnIndices (assignmentIndices I T (assignmentOnIndices X T A)) T A =
      assignmentOnIndices X T A := by
  apply ZFSet.ext
  intro z
  constructor
  · intro member
    obtain ⟨hA, inside⟩ := (mem_assignmentOnIndices _ T A z).1 member
    obtain ⟨t, ht, v, hv, w, hw, rfl⟩ := (mem_stageOneAssignments _ T z).1 inside
    rw [assignmentIndices_on] at ht
    exact (assignmentOnIndices_entry X T A t v w).2
      ⟨hA, (ZFSet.mem_inter.1 ht).2, hv, hw⟩
  · intro member
    have hA := ((mem_assignmentOnIndices X T A z).1 member).1
    obtain ⟨t, ht, v, hv, w, hw, rfl⟩ := (mem_stageOneAssignments I T z).1 (shape hA)
    exact (assignmentOnIndices_entry _ T A t v w).2
      ⟨hA, (mem_assignmentIndices I T (assignmentOnIndices X T A) t).2
        ⟨ht, v, hv, w, hw, member⟩, hv, hw⟩

end

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem assignmentQueryRelation_mem {I T C D : ZFSet.{u}}
    (hI : I ∈ M.sets) (hT : T ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets) :
    assignmentQueryRelation I T C D ∈ M.sets := by
  let f := productFirst I (ZFSet.prod T T)
  have hf : f ∈ M.sets := M.productFirst_mem pairing unions powers separation hI
    (M.prod_mem pairing unions powers separation hT hT)
  let params := extend I (extend f Fin.elim0)
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.assignmentQueryRelationFormula 0 1 2) params
    (Fin.cases hI (Fin.cases hf (fun j => Fin.elim0 j)))
    (M.prod_mem pairing unions powers separation hC hD)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.assignmentQueryRelationFormula 0 1 2) (extend z params))
      (ZFSet.prod C D) = assignmentQueryRelation I T C D := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, assignmentQueryRelation, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_assignmentQueryRelationFormula 0 1 2
      (extend z params) T rfl)
  exact equal ▸ selected

theorem realizedAssignmentQueries_mem {I T C D : ZFSet.{u}}
    (hI : I ∈ M.sets) (hT : T ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets) :
    realizedAssignmentQueries I T C D ∈ M.sets :=
  M.relationImage_mem separation hD hC (M.relationConverse_mem pairing unions powers separation
    hC hD (M.assignmentQueryRelation_mem pairing unions powers separation hI hT hC hD))

theorem exists_assignmentQuerySelector
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {I T C D : ZFSet.{u}} (hI : I ∈ M.sets) (hT : T ∈ M.sets)
    (hC : C ∈ M.sets) (hD : D ∈ M.sets) :
    ∃ F ∈ M.sets, ZFSet.IsFunc (realizedAssignmentQueries I T C D) D F ∧
      F ⊆ assignmentQueryRelation I T C D := by
  apply M.uniformize_relation pairing unions powers separation choice
    (M.realizedAssignmentQueries_mem pairing unions powers separation hI hT hC hD) hD
    (M.assignmentQueryRelation_mem pairing unions powers separation hI hT hC hD)
  intro q member
  exact ((mem_realizedAssignmentQueries I T C D q).1 member).2

theorem exists_stageOneAssignmentQuerySelector
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {rows I T D : ZFSet.{u}} (hRows : rows ∈ M.sets) (hI : I ∈ M.sets)
    (hT : T ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) (hD : D ∈ M.sets) :
    ∃ F ∈ M.sets,
      ZFSet.IsFunc (realizedAssignmentQueries I T (M.stageOneCandidateBound rows I T) D) D F ∧
      F ⊆ assignmentQueryRelation I T (M.stageOneCandidateBound rows I T) D :=
  M.exists_assignmentQuerySelector pairing unions powers separation choice hI hT
    (M.stageOneCandidateBound_mem pairing unions powers separation hRows hI hT omega) hD

end TransitiveGround

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem exists_groundOmegaOneClosure
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {I K : ZFSet.{u}} (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    {n : Nat} {f : (Fin (n + 1) → ZFSet.{u}) → ZFSet.{u}}
    (defined : GroundDefinableFunction M f) (params : Fin n → ZFSet.{u})
    (members : ∀ j, params j ∈ M.sets)
    (inflationary : ∀ X ∈ M.sets, X ⊆ I → X ⊆ f (extend X params))
    (preserves : ∀ X ∈ M.sets, X ⊆ I → GroundBelow M X K →
      f (extend X params) ⊆ I ∧ GroundBelow M (f (extend X params)) K) :
    let C := M.groundOmegaOne pairing unions powers separation collection infinite
    ∃ history ∈ M.sets,
      OrdinalRecursionTrace (fun alpha prior output =>
        output = f (extend (refinementHistoryIndices alpha prior) params)) C history ∧
      let X := refinementHistoryIndices C history
      X ∈ M.sets ∧ X ⊆ I ∧ GroundBelow M X K ∧
      (∀ alpha Y, ZFSet.pair alpha Y ∈ history →
        Y ∈ M.sets ∧ Y ⊆ I ∧ GroundBelow M Y K) ∧
      (∀ alpha beta Y Z, ZFSet.pair alpha Y ∈ history →
        ZFSet.pair beta Z ∈ history → alpha ∈ beta → Y ⊆ Z) ∧
      ∀ B ∈ M.sets, M.groundEmbeddable B ZFSet.omega → B ⊆ X →
        ∃ beta ∈ C,
          let U := refinementHistoryIndices beta history
          U ∈ M.sets ∧ U ⊆ X ∧ GroundBelow M U K ∧ B ⊆ U ∧ f (extend U params) ⊆ X := by
  let C := M.groundOmegaOne pairing unions powers separation collection infinite
  have spec := M.groundOmegaOne_spec pairing unions powers separation collection infinite
  have hC := spec.1
  obtain ⟨history, hh, trace⟩ := M.exists_historyUnionTrace pairing unions separation collection
    defined params members hC spec.2.1
  have bounds := M.historyUnionTrace_below pairing unions powers separation choice hK conditions
    (fun X => f (extend X params)) preserves C
    (conditions.groundOmegaOne_mem pairing unions powers separation collection infinite hK) history hh trace
  let X := refinementHistoryIndices C history
  have hX : X ∈ M.sets := M.refinementHistoryIndices_mem unions separation hC hh
  have step (beta Y : ZFSet.{u}) (entry : ZFSet.pair beta Y ∈ history) :
      Y = f (extend (refinementHistoryIndices beta history) params) := by
    have result := trace.2 beta (trace.1.pair_source entry) Y entry
    change Y = f (extend (refinementHistoryIndices beta (graphRestriction beta history)) params) at result
    rw [refinementHistoryIndices_restrict (fun _ hx => hx)] at result
    exact result
  have earlierUnion (beta : ZFSet.{u}) (member : beta ∈ C) :
      refinementHistoryIndices beta history ∈ M.sets ∧
      refinementHistoryIndices beta history ⊆ X ∧
      GroundBelow M (refinementHistoryIndices beta history) K := by
    have ground := M.refinementHistoryIndices_mem unions separation (M.transitive hC member) hh
    have subset := refinementHistoryIndices_mono (history := history) (spec.2.1.1 beta member)
    exact ⟨ground, subset, bounds.2.2.restrict separation ground hK subset⟩
  refine ⟨history, hh, trace, hX, bounds.2.1, bounds.2.2, ?_, ?_, ?_⟩
  · intro alpha Y entry
    exact ⟨M.transitive (M.union_mem unions (M.union_mem unions hh))
      (pair_second_mem_doubleUnion entry), bounds.1 alpha Y entry⟩
  · intro alpha beta Y Z first second before x inside
    have earlier := earlierUnion beta (trace.1.pair_source second)
    rw [step beta Z second]
    exact inflationary _ earlier.1 (fun _ hx => bounds.2.1 (earlier.2.1 hx))
      ((mem_refinementHistoryIndices beta history x).2 ⟨alpha, before, Y, first, inside⟩)
  · intro B hB small subset
    obtain ⟨beta, member, captured⟩ := M.historyUnion_countable_capture
      pairing unions powers separation collection infinite choice hh hB small subset
    have earlier := earlierUnion beta member
    refine ⟨beta, member, earlier.1, earlier.2.1, earlier.2.2, captured, ?_⟩
    obtain ⟨Y, entry⟩ := trace.1.total member
    rw [← step beta Y entry]
    intro x inside
    exact (mem_refinementHistoryIndices C history x).2 ⟨beta, member, Y, entry, inside⟩

theorem assignmentQueryClosure_representatives
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {rows I T D c X : ZFSet.{u}} (hI : I ∈ M.sets) (hT : T ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) (hX : X ∈ M.sets)
    (shape : D ⊆ M.stageOneCandidateBound rows I T)
    (selector : ZFSet.IsFunc
      (realizedAssignmentQueries I T (M.stageOneCandidateBound rows I T) D) D c)
    (selected : c ⊆ assignmentQueryRelation I T (M.stageOneCandidateBound rows I T) D)
    (capture : ∀ B ∈ M.sets, M.groundEmbeddable B ZFSet.omega → B ⊆ X →
      ∃ U, B ⊆ U ∧ representativeIndexStep I T
        (realizedAssignmentQueries I T (M.stageOneCandidateBound rows I T) D) c U ⊆ X) :
    ∀ row A, ZFSet.pair row A ∈ D →
      ∃ C, ZFSet.pair row C ∈ D ∧ assignmentIndices I T C ⊆ X ∧
        assignmentOnIndices (assignmentIndices I T (assignmentOnIndices X T A)) T C =
          assignmentOnIndices X T A := by
  intro row A member
  let L := assignmentOnIndices X T A
  let B := assignmentIndices I T L
  let Q := realizedAssignmentQueries I T (M.stageOneCandidateBound rows I T) D
  have data := (M.pair_mem_stageOneCandidateBound rows I T row A).1 (shape member)
  have hL : L ∈ M.sets := M.assignmentOnIndices_mem pairing unions powers separation hX hT data.2.1
  have smallL := M.assignmentOnIndices_small pairing unions powers separation hX hT data.2.1
    omega data.2.2.2
  have listShape : L ⊆ stageOneAssignments I T :=
    fun _ h => data.2.2.1 ((mem_assignmentOnIndices X T A _).1 h).1
  have queryCandidate : ZFSet.pair row L ∈ M.stageOneCandidateBound rows I T :=
    (M.pair_mem_stageOneCandidateBound rows I T row L).2 ⟨data.1, hL, listShape, smallL⟩
  have query : ZFSet.pair row L ∈ Q :=
    (mem_realizedAssignmentQueries I T (M.stageOneCandidateBound rows I T) D _).2
      ⟨queryCandidate, ZFSet.pair row A, member,
        (assignmentQueryRelation_entry I T (M.stageOneCandidateBound rows I T) D row L row A).2
          ⟨queryCandidate, member, rfl, assignmentOnIndices_indices_on data.2.2.1⟩⟩
  have hB : B ∈ M.sets := M.assignmentIndices_mem pairing unions powers separation hI hT hL
  have smallB := M.assignmentIndices_small pairing unions powers separation choice hI hT hL omega smallL
  have subsetB : B ⊆ X := by
    intro i hi
    change i ∈ assignmentIndices I T (assignmentOnIndices X T A) at hi
    rw [assignmentIndices_on] at hi
    exact (ZFSet.mem_inter.1 hi).2
  obtain ⟨U, captured, closed⟩ := capture B hB smallB subsetB
  obtain ⟨p, entry, _⟩ := selector.2 (ZFSet.pair row L) query
  have inD := (ZFSet.pair_mem_prod.1 (selector.1 entry)).2
  obtain ⟨other, _, C, _, _, _, rfl⟩ :=
    (M.mem_stageOneCandidateBound rows I T p).1 (shape inD)
  have matched := (assignmentQueryRelation_entry I T (M.stageOneCandidateBound rows I T) D
    row L other C).1 (selected entry)
  obtain rfl := matched.2.2.1
  refine ⟨C, inD, ?_, matched.2.2.2⟩
  have localQuery : AssignmentQueryWithin U T (ZFSet.pair row L) :=
    ⟨row, L, rfl, (assignment_subset_iff_indices_subset listShape).2 captured⟩
  exact fun _ h => closed (representativeIndexStep_covers query localQuery entry h)

theorem exists_assignmentRepresentativeClosure
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {rows I T D K : ZFSet.{u}} (hRows : rows ∈ M.sets) (hI : I ∈ M.sets)
    (hT : T ∈ M.sets) (hD : D ∈ M.sets) (hK : K ∈ M.sets)
    (conditions : GroundInaccessibleConditions M K)
    (smallRows : GroundBelow M rows K) (smallT : GroundBelow M T K)
    (shape : D ⊆ M.stageOneCandidateBound rows I T) :
    ∃ X ∈ M.sets, X ⊆ I ∧ GroundBelow M X K ∧
      ∀ row A, ZFSet.pair row A ∈ D →
        ∃ C, ZFSet.pair row C ∈ D ∧ assignmentIndices I T C ⊆ X ∧
          assignmentOnIndices (assignmentIndices I T (assignmentOnIndices X T A)) T C =
            assignmentOnIndices X T A := by
  have omega := M.omega_mem separation infinite
  let Q := realizedAssignmentQueries I T (M.stageOneCandidateBound rows I T) D
  have hQ : Q ∈ M.sets := M.realizedAssignmentQueries_mem pairing unions powers separation hI hT
    (M.stageOneCandidateBound_mem pairing unions powers separation hRows hI hT omega) hD
  have queries : Q ⊆ M.stageOneCandidateBound rows I T :=
    fun _ h => ((mem_realizedAssignmentQueries I T (M.stageOneCandidateBound rows I T) D _).1 h).1
  obtain ⟨c, hc, selector, selected⟩ := M.exists_stageOneAssignmentQuerySelector
    pairing unions powers separation choice hRows hI hT omega hD
  let params : Fin 4 → ZFSet.{u} := extend I (extend T (extend Q (extend c Fin.elim0)))
  have members : ∀ j, params j ∈ M.sets :=
    Fin.cases hI (Fin.cases hT (Fin.cases hQ (Fin.cases hc (fun j => Fin.elim0 j))))
  have inflationary : ∀ X ∈ M.sets, X ⊆ I →
      X ⊆ representativeIndexStep I T Q c X :=
    fun X _ _ => representativeIndexStep_contains I T Q c X
  have preserves : ∀ X ∈ M.sets, X ⊆ I → GroundBelow M X K →
      representativeIndexStep I T Q c X ⊆ I ∧
        GroundBelow M (representativeIndexStep I T Q c X) K := by
    intro X hX subset smallX
    exact ⟨representativeIndexStep_subset subset,
      M.representativeIndexStep_below pairing unions powers separation infinite choice
        hRows hI hT hQ hc hD hX hK conditions selector queries shape smallRows smallT smallX⟩
  obtain ⟨history, _, _, hX, subsetX, smallX, _, _, capture⟩ :=
    M.exists_groundOmegaOneClosure pairing unions powers separation collection infinite choice
      hK conditions (M.definable_representativeIndexStep pairing unions separation)
      params members inflationary preserves
  refine ⟨_, hX, subsetX, smallX,
    M.assignmentQueryClosure_representatives pairing unions powers separation choice
      hI hT omega hX shape selector selected ?_⟩
  intro B hB countable subset
  obtain ⟨beta, _, _, _, _, bounded, closed⟩ := capture B hB countable subset
  exact ⟨refinementHistoryIndices beta history, bounded, closed⟩

end TransitiveGround

end PartitionPilot.Forcing

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

theorem semanticStructuralTrace_antichains_below
    {K history : ZFSet.{u}} (hK : K ∈ M.sets) (hh : history ∈ M.sets)
    (conditions : GroundInaccessibleConditions M K)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 level prior) K history)
    (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (smallRows : GroundBelow M c.carrier K) (smallT : GroundBelow M T K) :
    let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 K history
    ∀ D ∈ M.sets,
      OrderAntichainCode (M.refinementHistoryForcing c.carrier T K packed)
        (M.refinementHistoryOrder c.carrier c.conditionOrder T K packed) D → GroundBelow M D K := by
  dsimp only
  intro D hD antichain
  let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 K history
  let I := refinementDataHistoryIndices K packed
  let Q := M.refinementHistoryForcing c.carrier T K packed
  have hPacked : packed ∈ M.sets := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, K, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hK (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hI : I ∈ M.sets := M.refinementDataHistoryIndices_mem pairing unions powers separation hK hPacked
  have shape : Q ⊆ M.stageOneCandidateBound c.carrier I T :=
    fun _ member => ((M.mem_refinementHistoryForcing c.carrier T K packed _).1 member).1
  obtain ⟨X, hX, _, smallX, representatives⟩ := M.exists_assignmentRepresentativeClosure
    pairing unions powers separation collection infinite choice carrier hI hT hD hK conditions
    smallRows smallT (fun _ member => shape (antichain.1 member))
  apply M.representative_antichain_below pairing unions powers separation carrier hX hT hK hD omega
    conditions.1 conditions.2.2.2 smallRows smallX smallT shape antichain ?_ representatives
  intro row A C first second agreement
  obtain ⟨member, belowFirst, belowSecond⟩ := M.semanticStructuralTrace_binary_union_extension
    c a t b d base directed T T2 rowTop pairing unions powers separation collection
    carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega
    valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh conditions.1 trace
    infinite choice row A C first second agreement
  exact ⟨ZFSet.pair row (A ∪ C), member, belowFirst, belowSecond⟩

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

theorem semanticStructuralTrace_predense_prefix
    {stages history : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (ordinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
    (alpha : ZFSet.{u}) (hAlpha : alpha ∈ M.sets)
    (cutOrdinal : ordinalSetProperty alpha) (subset : alpha ⊆ stages)
    (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0) :
    let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 stages history
    let U := M.refinementHistoryForcing c.carrier T stages packed
    let L := M.refinementHistoryForcing c.carrier T alpha (graphRestriction alpha packed)
    ∀ A : ZFSet.{u}, A ⊆ L →
      (∀ q ∈ U, ∃ p ∈ A, ∃ r ∈ U,
        ZFSet.pair r q ∈ M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed ∧
        ZFSet.pair r p ∈ M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed) →
      ∀ q ∈ L, ∃ p ∈ A, ∃ r ∈ L,
        ZFSet.pair r q ∈ M.refinementHistoryOrder c.carrier c.conditionOrder T alpha
          (graphRestriction alpha packed) ∧
        ZFSet.pair r p ∈ M.refinementHistoryOrder c.carrier c.conditionOrder T alpha
          (graphRestriction alpha packed) := by
  let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history
  let U := M.refinementHistoryForcing c.carrier T stages packed
  let L := M.refinementHistoryForcing c.carrier T alpha (graphRestriction alpha packed)
  let run := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix)
    T T2 ordinal trace
  let witnesses := M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace
  let mono := M.structuralHistory_rawTests_mono t b d base directed T T2 stages history
    pairing unions powers separation collection group nodes supports hh hT witnesses
  have hPacked : packed ∈ M.sets := M.structuralRefinementHistory_mem
    pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
  have projection := M.semanticStructuralTrace_completeProjection c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace alpha hAlpha cutOrdinal subset infinite choice
  have unchanged : ∀ q : SetMembers L,
      (SetMembers.presentation U).encode
        (run.inclusion ordinal cutOrdinal subset pairing unions powers separation infinite choice
          hs hPacked hT hAlpha carrier rowTop topMem topRows mono c.conditionOrder_code q) =
        (SetMembers.presentation L).encode q := by
    intro q
    exact run.inclusionFunction_raw ordinal cutOrdinal subset pairing unions powers separation
      infinite choice hs hPacked hT hAlpha carrier rowTop topMem topRows mono q
  dsimp only
  intro A within predense
  have upperOrder : (SetMembers.presentation U).conditionOrder =
      M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed :=
    M.refinementHistoryDecodedOrder_eq c.conditionOrder_code T stages packed
  have lowerOrder : (SetMembers.presentation L).conditionOrder =
      M.refinementHistoryOrder c.carrier c.conditionOrder T alpha (graphRestriction alpha packed) :=
    M.refinementHistoryDecodedOrder_eq c.conditionOrder_code T alpha (graphRestriction alpha packed)
  have upper : ∀ q ∈ (SetMembers.presentation U).carrier, ∃ p ∈ A,
      ∃ r ∈ (SetMembers.presentation U).carrier,
        ZFSet.pair r q ∈ (SetMembers.presentation U).conditionOrder ∧
        ZFSet.pair r p ∈ (SetMembers.presentation U).conditionOrder := by
    rw [upperOrder]
    exact predense
  have result := projection.raw_predense_restriction
    (SetMembers.presentation U) (SetMembers.presentation L) unchanged within upper
  rw [lowerOrder] at result
  exact result

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

theorem semanticStructuralTrace_membershipAntichains_prefix
    {K history : ZFSet.{u}} (hK : K ∈ M.sets) (hh : history ∈ M.sets)
    (conditions : GroundInaccessibleConditions M K)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 level prior) K history)
    (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (smallRows : GroundBelow M c.carrier K) (smallT : GroundBelow M T K) :
    let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 K history
    let Q := M.refinementHistoryForcing c.carrier T K packed
    let order := M.refinementHistoryOrder c.carrier c.conditionOrder T K packed
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T K packed
    let s := SetMembers.presentation Q
    ∀ J ∈ M.sets, GroundBelow M J K → (∀ sigma ∈ J, IsName s sigma) →
      ∀ tau : (M.nameDomain s).names,
        ∃ f ∈ M.sets, ZFSet.IsFunc J (M.groundPower Q) f ∧
          (∀ sigma A, ZFSet.pair sigma A ∈ f →
            RelativeMaximalAntichainCode Q order
              (M.ordinaryMembershipDecisions Q order sigma tau.val.val) A ∧
            ∀ q ∈ Q, ∃ p ∈ A, ∃ r ∈ Q,
              ZFSet.pair r q ∈ order ∧ ZFSet.pair r p ∈ order) ∧
          let U := (relationImage J (M.groundPower Q) f).sUnion
          (U ∈ M.sets ∧ GroundBelow M U K ∧ U ⊆ Q) ∧
          ∃ beta ∈ K,
            (∀ row B, ZFSet.pair row B ∈ U →
              assignmentCut (refinementDataHistoryLevels K packed T) beta B = B ∧
              ZFSet.pair row B ∈ M.refinementHistoryForcing c.carrier T beta (graphRestriction beta packed)) ∧
            ∀ sigma A, ZFSet.pair sigma A ∈ f →
              let lower := M.refinementHistoryForcing c.carrier T beta (graphRestriction beta packed)
              let lowerOrder := M.refinementHistoryOrder c.carrier c.conditionOrder T beta
                (graphRestriction beta packed)
              A ⊆ lower ∧ ∀ q ∈ lower, ∃ p ∈ A, ∃ r ∈ lower,
                ZFSet.pair r q ∈ lowerOrder ∧ ZFSet.pair r p ∈ lowerOrder := by
  let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 K history
  let Q := M.refinementHistoryForcing c.carrier T K packed
  let order := M.refinementHistoryOrder c.carrier c.conditionOrder T K packed
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T K packed
  let s := SetMembers.presentation Q
  have hPacked : packed ∈ M.sets := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, K, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hK (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hQ : Q ∈ M.sets := M.refinementHistoryForcing_mem
    pairing unions powers separation carrier hT hK hPacked omega
  have orderEq : s.conditionOrder = order :=
    M.refinementHistoryDecodedOrder_eq c.conditionOrder_code T K packed
  have hOrder : s.conditionOrder ∈ M.sets := orderEq.symm ▸
    M.refinementHistoryOrder_mem pairing unions powers separation carrier rowOrderGround hT hK hPacked omega
  have chain := M.semanticStructuralTrace_antichains_below c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hK hh conditions trace infinite choice smallRows smallT
  have typedChain : ∀ A ∈ M.sets, OrderAntichainCode s.carrier s.conditionOrder A → GroundBelow M A K := by
    rw [orderEq]
    exact chain
  dsimp only
  intro J hJ smallJ valid tau
  have family := M.exists_ordinaryMembershipAntichainFamily s pairing unions powers separation
    collection choice hQ hOrder hJ valid tau hK conditions smallJ typedChain
  rw [orderEq] at family
  obtain ⟨f, hf, function, selected, whole⟩ := family
  let U := (relationImage J (M.groundPower Q) f).sUnion
  obtain ⟨beta, hBeta, placed⟩ := M.structuralForcingTrace_small_family_prefix
    c.carrier c.conditionOrder rowTop (a.actionGraph c t) t.carrier b.carrier b.conditionOrder
    (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2
    pairing unions powers separation collection choice carrier group nodes nodeOrder supports hT hT2
    hK hh conditions trace U whole.1 whole.2.1 whole.2.2
  refine ⟨f, hf, function, selected, whole, beta, hBeta, placed, ?_⟩
  intro sigma A entry
  have values := ZFSet.pair_mem_prod.1 (function.1 entry)
  have insideUnion : A ⊆ U := fun q hq => ZFSet.mem_sUnion.2
    ⟨A, (mem_relationImage J (M.groundPower Q) f A).2
      ⟨values.2, sigma, values.1, entry⟩, hq⟩
  have lower : A ⊆ M.refinementHistoryForcing c.carrier T beta (graphRestriction beta packed) := by
    intro q hq
    have inU := insideUnion hq
    have inQ := whole.2.2 inU
    have candidate := ((M.mem_refinementHistoryForcing c.carrier T K packed q).1 inQ).1
    obtain ⟨row, _, B, _, _, _, rfl⟩ := (M.mem_stageOneCandidateBound c.carrier
      (refinementDataHistoryIndices K packed) T q).1 candidate
    exact (placed row B inU).2
  refine ⟨lower, ?_⟩
  exact M.semanticStructuralTrace_predense_prefix c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hK hh conditions.1 trace beta (M.transitive hK hBeta)
    (ordinalSetProperty_member conditions.1 hBeta) (conditions.1.1 beta hBeta) infinite choice
    A lower (selected sigma A entry).2

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

theorem semanticStructuralTrace_finitePowerAntichains_prefix
    {K history : ZFSet.{u}} (hK : K ∈ M.sets) (hh : history ∈ M.sets)
    (standard : GroundStandardInaccessible M K)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 level prior) K history)
    (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (smallRows : GroundBelow M c.carrier K) (smallT : GroundBelow M T K) (n : Nat) :
    let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 K history
    let Q := M.refinementHistoryForcing c.carrier T K packed
    let order := M.refinementHistoryOrder c.carrier c.conditionOrder T K packed
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T K packed
    let s := SetMembers.presentation Q
    let J := iteratedPairNameFamily (ZFSet.pair rowTop ∅) T n
    J ∈ M.sets ∧ GroundBelow M J K ∧
      (∀ alpha : ZFSet.{u}, ordinalSetProperty alpha → alpha ⊆ K →
        ∀ z ∈ J, IsName (SetMembers.presentation (M.refinementHistoryForcing
          c.carrier T alpha (graphRestriction alpha packed))) z) ∧
      ∀ tau : (M.nameDomain s).names,
        ∃ f ∈ M.sets, ZFSet.IsFunc J (M.groundPower Q) f ∧
          (∀ sigma A, ZFSet.pair sigma A ∈ f →
            RelativeMaximalAntichainCode Q order
              (M.ordinaryMembershipDecisions Q order sigma tau.val.val) A ∧
            ∀ q ∈ Q, ∃ p ∈ A, ∃ r ∈ Q,
              ZFSet.pair r q ∈ order ∧ ZFSet.pair r p ∈ order) ∧
          let U := (relationImage J (M.groundPower Q) f).sUnion
          (U ∈ M.sets ∧ GroundBelow M U K ∧ U ⊆ Q) ∧
          ∃ beta ∈ K,
            (∀ row B, ZFSet.pair row B ∈ U →
              assignmentCut (refinementDataHistoryLevels K packed T) beta B = B ∧
              ZFSet.pair row B ∈ M.refinementHistoryForcing c.carrier T beta (graphRestriction beta packed)) ∧
            ∀ sigma A, ZFSet.pair sigma A ∈ f →
              let lower := M.refinementHistoryForcing c.carrier T beta (graphRestriction beta packed)
              let lowerOrder := M.refinementHistoryOrder c.carrier c.conditionOrder T beta
                (graphRestriction beta packed)
              A ⊆ lower ∧ ∀ q ∈ lower, ∃ p ∈ A, ∃ r ∈ lower,
                ZFSet.pair r q ∈ lowerOrder ∧ ZFSet.pair r p ∈ lowerOrder := by
  let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 K history
  let J := iteratedPairNameFamily (ZFSet.pair rowTop ∅) T n
  let run := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
    (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 standard.1.1 trace
  have terms := M.structuralTrace_finitePowerTerms c c.conditionOrder rowTop
    (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 pairing unions powers separation
    carrier hT valid1 topMem standard.1.1 trace n
  have oneGround := M.orderedPair_mem pairing (M.transitive carrier topMem)
    (M.empty_mem ⟨c.carrier, carrier⟩)
  have smallJ := M.iteratedPairNameFamily_below pairing unions powers separation infinite
    choice oneGround hT hK standard smallT n
  have upperValid := terms.2 K standard.1.1 (fun _ h => h)
  rw [run.carriers.data.function.restriction_eq] at upperValid
  have family := M.semanticStructuralTrace_membershipAntichains_prefix c a t b d base directed
    T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction
    group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hK hh
    (standard.to_conditions pairing unions powers separation hK) trace infinite choice smallRows smallT
    J terms.1 smallJ upperValid
  exact ⟨terms.1, smallJ, terms.2, family⟩

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
include hK hh standard trace infinite choice smallRows smallT

theorem semanticStructuralTrace_commonPowerAntichains_oai :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T K packed
    ∀ count (degrees : Fin count → Nat)
      (tau : Fin count → (M.nameDomain (SetMembers.presentation Q)).names),
      ∃ beta, ∃ _ : beta ∈ K, ∃ f : Fin count → ZFSet.{u}, ∀ i,
        let J := iteratedPairNameFamily (ZFSet.pair rowTop ∅) T (degrees i)
        f i ∈ M.sets ∧ ZFSet.IsFunc J (M.groundPower Q) (f i) ∧
        (∀ sigma A, ZFSet.pair sigma A ∈ f i →
          RelativeMaximalAntichainCode Q
            (M.refinementHistoryOrder c.carrier c.conditionOrder T K packed)
            (M.ordinaryMembershipDecisions Q
              (M.refinementHistoryOrder c.carrier c.conditionOrder T K packed)
              sigma (tau i).val.val) A ∧
          ∀ q ∈ Q, ∃ p ∈ A, ∃ r ∈ Q,
            ZFSet.pair r q ∈ M.refinementHistoryOrder c.carrier c.conditionOrder T K packed ∧
            ZFSet.pair r p ∈ M.refinementHistoryOrder c.carrier c.conditionOrder T K packed) ∧
        (∀ sigma A, ZFSet.pair sigma A ∈ f i →
          let lower := M.refinementHistoryForcing c.carrier T beta (graphRestriction beta packed)
          let lowerOrder := M.refinementHistoryOrder c.carrier c.conditionOrder T beta
            (graphRestriction beta packed)
          A ⊆ lower ∧ ∀ q ∈ lower, ∃ p ∈ A, ∃ r ∈ lower,
            ZFSet.pair r q ∈ lowerOrder ∧ ZFSet.pair r p ∈ lowerOrder) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T K packed
  intro count degrees tau
  let J : Fin count → ZFSet.{u} := fun i =>
    iteratedPairNameFamily (ZFSet.pair rowTop ∅) T (degrees i)
  have each : ∀ i : Fin count, ∃ f ∈ M.sets,
      ZFSet.IsFunc (J i) (M.groundPower Q) f ∧
      (∀ sigma A, ZFSet.pair sigma A ∈ f →
        RelativeMaximalAntichainCode Q
          (M.refinementHistoryOrder c.carrier c.conditionOrder T K packed)
          (M.ordinaryMembershipDecisions Q
            (M.refinementHistoryOrder c.carrier c.conditionOrder T K packed)
            sigma (tau i).val.val) A ∧
        ∀ q ∈ Q, ∃ p ∈ A, ∃ r ∈ Q,
          ZFSet.pair r q ∈ M.refinementHistoryOrder c.carrier c.conditionOrder T K packed ∧
          ZFSet.pair r p ∈ M.refinementHistoryOrder c.carrier c.conditionOrder T K packed) ∧
      let U := (relationImage (J i) (M.groundPower Q) f).sUnion
      U ∈ M.sets ∧ GroundBelow M U K ∧ U ⊆ Q := by
    intro i
    obtain ⟨_, _, _, family⟩ := M.semanticStructuralTrace_finitePowerAntichains_prefix
      c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh standard trace infinite choice smallRows smallT (degrees i)
    obtain ⟨f, hf, function, selected, whole, _⟩ := family (tau i)
    exact ⟨f, hf, function, selected, whole⟩
  choose f hf function selected whole using each
  let U : Fin count → ZFSet.{u} := fun i => (relationImage (J i) (M.groundPower Q) (f i)).sUnion
  let conditions := standard.to_conditions pairing unions powers separation hK
  obtain ⟨D, hD, smallD, members⟩ := conditions.finite_family_union
    pairing unions powers separation infinite choice hK count U
    (fun i => ⟨(whole i).1, (whole i).2.1⟩)
  have inside : D ⊆ Q := by
    intro q hq
    obtain ⟨i, member⟩ := (members q).1 hq
    exact (whole i).2.2 member
  obtain ⟨beta, hBeta, placed⟩ := M.structuralForcingTrace_small_family_prefix
    c.carrier c.conditionOrder rowTop (a.actionGraph c t) t.carrier b.carrier b.conditionOrder
    (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2
    pairing unions powers separation collection choice carrier group nodes nodeOrder supports hT hT2
    hK hh conditions trace D hD smallD inside
  refine ⟨beta, hBeta, f, ?_⟩
  intro i
  refine ⟨hf i, function i, selected i, ?_⟩
  intro sigma A entry
  have values := ZFSet.pair_mem_prod.1 ((function i).1 entry)
  have insideUnion : A ⊆ D := by
    intro q hq
    apply (members q).2
    refine ⟨i, ZFSet.mem_sUnion.2 ?_⟩
    exact ⟨A, (mem_relationImage (J i) (M.groundPower Q) (f i) A).2
      ⟨values.2, sigma, values.1, entry⟩, hq⟩
  have lower : A ⊆ M.refinementHistoryForcing c.carrier T beta (graphRestriction beta packed) := by
    intro q hq
    have inD := insideUnion hq
    have inQ := inside inD
    have candidate := ((M.mem_refinementHistoryForcing c.carrier T K packed q).1 inQ).1
    obtain ⟨row, _, B, _, _, _, rfl⟩ := (M.mem_stageOneCandidateBound c.carrier
      (refinementDataHistoryIndices K packed) T q).1 candidate
    exact (placed row B inD).2
  refine ⟨lower, ?_⟩
  exact M.semanticStructuralTrace_predense_prefix c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hK hh conditions.1 trace beta (M.transitive hK hBeta)
    (ordinalSetProperty_member conditions.1 hBeta) (conditions.1.1 beta hBeta) infinite choice
    A lower (selected i sigma A entry).2

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

theorem solution.{u} : type_of% @OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralTrace_commonPowerAntichains_oai.{u} := @OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralTrace_commonPowerAntichains_oai.{u}
