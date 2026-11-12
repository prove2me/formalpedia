-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.GroundInitialMainSuccessorData.exists_rankedTargetSerialization
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:05:43.113898+00:00
-- url     : https://prove2.me/submissions/b35cf58b-4374-457b-ba70-1250f5516d33

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
import Definitions.Def_OAIQ253P006
import Definitions.Def_OAIQ253P007

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

theorem rank_constantFamilyGraph_lt {I x : ZFSet.{u}}
    (domain : ZFSet.rank I < o) (value : ZFSet.rank x < o) :
    ZFSet.rank (constantFamilyGraph I x) < o :=
  rank_functionGraph_lt limit (constantFamilyGraph_function I x) domain
    (rank_singleton_lt limit value)

end PartitionPilot.Forcing

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundNaturalFamilyShift
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing



open SetFormula
universe u

theorem naturalFamilyShift_entries (family : ZFSet.{u}) (n : Nat) (y : ZFSet.{u}) :
    ZFSet.pair (natSetCode n) y ∈ naturalFamilyShift family ↔
      ZFSet.pair (natSetCode (n + 1)) y ∈ family := by
  rw [naturalFamilyShift, pair_mem_relationCompose]
  constructor
  · rintro ⟨_, _, k, hk, next, entry⟩
    obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode k).1 hk
    exact (pair_mem_natSuccessorGraph n k).1 next ▸ entry
  · intro entry
    exact ⟨natSetCode_mem_omega n, pair_second_mem_doubleUnion entry,
      natSetCode (n + 1), natSetCode_mem_omega (n + 1),
      (pair_mem_natSuccessorGraph n (n + 1)).2 rfl, entry⟩

theorem naturalFamilyShift_function {family : ZFSet.{u}}
    (function : FunctionGraphOn ZFSet.omega family) :
    FunctionGraphOn ZFSet.omega (naturalFamilyShift family) := by
  have bounded : ZFSet.IsFunc ZFSet.omega family.sUnion.sUnion family := by
    refine ⟨?_, function.to_isFunc.2⟩
    intro z hz
    obtain ⟨x, hx, y, _, rfl⟩ := ZFSet.mem_prod.1 (function.to_isFunc.1 hz)
    exact ZFSet.pair_mem_prod.2 ⟨hx, pair_second_mem_doubleUnion hz⟩
  exact ⟨_, relationCompose_function_of_subset natSuccessorGraph_isFunc bounded (fun _ h => h)⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem naturalFamilyShift_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {family : ZFSet.{u}} (hFamily : family ∈ M.sets) : naturalFamilyShift family ∈ M.sets :=
  M.relationCompose_mem pairing unions powers separation (M.omega_mem separation infinite)
    (M.omega_mem separation infinite) (M.union_mem unions (M.union_mem unions hFamily))
    (M.natSuccessorGraph_mem pairing unions powers separation infinite) hFamily

end TransitiveGround


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





namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_naturalStepFormula {k : Nat} (φ : SetFormula (k + 2))
    (params : Fin k → ZFSet.{u}) (members : ∀ i, params i ∈ M.sets)
    {a p y base : ZFSet.{u}} (ha : a ∈ M.sets) (hp : p ∈ M.sets)
    (hy : y ∈ M.sets) (hb : base ∈ M.sets) :
    Realize M.sets (naturalStepFormula φ) (extend a (extend p (extend y (extend base params)))) ↔
      (a = ∅ ∧ y = base) ∨ ∃ m ∈ M.sets, ∃ x ∈ M.sets,
        a = insert m m ∧ ZFSet.pair m x ∈ p ∧
          Realize M.sets φ (extend x (extend y params)) := by
  have mem4 : ∀ i, extend a (extend p (extend y (extend base params))) i ∈ M.sets :=
    Fin.cases ha (Fin.cases hp (Fin.cases hy (Fin.cases hb members)))
  rw [naturalStepFormula, realize_disj]
  apply or_congr
  · change (Realize M.sets (BoundedFormula.emptyFormula 0).toFormula _ ∧ y = base) ↔ _
    exact and_congr ((BoundedFormula.realize_toFormula M _ _ mem4).trans
      (BoundedFormula.truth_emptyFormula _ _)) Iff.rfl
  · rw [realize_ex]
    apply exists_congr
    intro m
    apply and_congr_right
    intro hm
    rw [realize_ex]
    apply exists_congr
    intro x
    apply and_congr_right
    intro hx
    have mem6 : ∀ i, extend x (extend m (extend a (extend p (extend y (extend base params))))) i ∈ M.sets :=
      Fin.cases hx (Fin.cases hm mem4)
    change (Realize M.sets (BoundedFormula.successorFormula 2 1).toFormula _ ∧
      Realize M.sets (BoundedFormula.pairMembershipFormula 1 0 3).toFormula _ ∧ _) ↔ _
    rw [BoundedFormula.realize_toFormula M _ _ mem6, BoundedFormula.truth_successorFormula,
      BoundedFormula.realize_toFormula M _ _ mem6, BoundedFormula.truth_pairMembershipFormula,
      realize_reindex, map_extend, map_extend]
    rfl

end TransitiveGround

theorem natSetCode_succ_eq_insert_iff (n : Nat) (x : ZFSet.{u}) :
    natSetCode (n + 1) = insert x x ↔ x = natSetCode n := by
  constructor
  · intro equal
    have member : x ∈ natSetCode (n + 1) := equal.symm ▸ ZFSet.mem_insert x x
    obtain ⟨j, _, rfl⟩ := (mem_natSetCode x (n + 1)).1 member
    have codes : natSetCode (n + 1) = natSetCode (j + 1) := equal
    exact congrArg natSetCode (Nat.add_right_cancel (natSetCode_injective codes)).symm
  · rintro rfl
    rfl


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

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem layerBirthFiber_mem (separation : SeparationSchema M.sets) {L birth t : ZFSet.{u}}
    (hL : L ∈ M.sets) (hBirth : birth ∈ M.sets) (ht : t ∈ M.sets) :
    layerBirthFiber L birth t ∈ M.sets := by
  let params := extend t (extend birth Fin.elim0)
  have selected := M.bounded_separation_mem separation (BoundedFormula.pairMembershipFormula 0 1 2)
    params (Fin.cases ht (Fin.cases hBirth (fun i => Fin.elim0 i))) hL
  have eq : ZFSet.sep (fun x => BoundedFormula.Truth (BoundedFormula.pairMembershipFormula 0 1 2)
      (extend x params)) L = layerBirthFiber L birth t := by
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_sep, mem_layerBirthFiber]
    exact and_congr Iff.rfl (BoundedFormula.truth_pairMembershipFormula 0 1 2 _)
  exact eq ▸ selected
end TransitiveGround

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

theorem rank_equivalenceClasses_lt {A : ZFSet.{u}} (E : ZFSet.{u})
    (carrier : ZFSet.rank A < o) : ZFSet.rank (equivalenceClasses A E) < o := by
  have subset : equivalenceClasses A E ⊆ ZFSet.powerset A :=
    fun _ hx => (ZFSet.mem_sep.1 hx).1
  have bound := ZFSet.rank_mono subset
  rw [ZFSet.rank_powerset] at bound
  exact bound.trans_lt (limit.succ_lt carrier)

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundCompressionStampBounds
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
universe u

theorem compressionStamp_ordinal {base : ZFSet.{u}} (ordinal : ordinalSetProperty base) (n : Nat) :
    ordinalSetProperty (compressionStamp base n) := by
  induction n with
  | zero => exact ordinalSetProperty_succ ordinal
  | succ n ih => exact ordinalSetProperty_succ ih

theorem compressionStamp_union_ordinal {base limit : ZFSet.{u}}
    (ordinal : ordinalSetProperty base) (union : NatUnionCode (compressionStamp base) limit) :
    ordinalSetProperty limit := by
  constructor
  · intro y hy z hz
    obtain ⟨n, yn⟩ := (union y).1 hy
    exact union.subset n ((compressionStamp_ordinal ordinal n).1 y yn z hz)
  · intro y hy
    obtain ⟨n, yn⟩ := (union y).1 hy
    exact (compressionStamp_ordinal ordinal n).2 y yn

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open scoped ZFSet
universe u

namespace FunctionGraphOn
variable {family : ZFSet.{u}}

theorem natValue_entry_iff (function : FunctionGraphOn ZFSet.omega family) (n : Nat) (y : ZFSet.{u}) :
    ZFSet.pair (natSetCode n) y ∈ family ↔ y = function.natValue n := by
  constructor
  · exact fun entry => function.unique entry (function.natValue_entry n)
  · exact fun equal => equal.symm ▸ function.natValue_entry n

end FunctionGraphOn

theorem naturalFamilyUnion_code {family : ZFSet.{u}}
    (function : FunctionGraphOn ZFSet.omega family) :
    NatUnionCode function.natValue (naturalFamilyUnion family) := by
  intro x
  rw [naturalFamilyUnion, ZFSet.mem_sUnion]
  constructor
  · rintro ⟨value, member, hx⟩
    obtain ⟨_, index, hi, entry⟩ := (mem_relationImage _ _ _ value).1 member
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode index).1 hi
    exact ⟨n, ((function.natValue_entry_iff n value).1 entry) ▸ hx⟩
  · rintro ⟨n, hx⟩
    have entry := function.natValue_entry n
    exact ⟨function.natValue n, (mem_relationImage _ _ _ _).2
      ⟨pair_second_mem_doubleUnion entry, natSetCode n, natSetCode_mem_omega n, entry⟩, hx⟩

namespace TransitiveGround
open SetFormula

theorem naturalFamilyUnion_mem (M : TransitiveGround.{u})
    (unions : Realize M.sets SetFormula.union Fin.elim0) (separation : SeparationSchema M.sets)
    (hω : (ZFSet.omega : ZFSet.{u}) ∈ M.sets) {family : ZFSet.{u}} (hFamily : family ∈ M.sets) :
    naturalFamilyUnion family ∈ M.sets :=
  M.union_mem unions (M.relationImage_mem separation hω
    (M.union_mem unions (M.union_mem unions hFamily)) hFamily)

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem realize_naturalStep_zero {k : Nat} (φ : SetFormula (k + 2))
    (params : Fin k → ZFSet.{u}) (members : ∀ i, params i ∈ M.sets)
    {p y base : ZFSet.{u}} (hzero : natSetCode 0 ∈ M.sets)
    (hp : p ∈ M.sets) (hy : y ∈ M.sets) (hb : base ∈ M.sets) :
    Realize M.sets (naturalStepFormula φ)
      (extend (natSetCode 0) (extend p (extend y (extend base params)))) ↔ y = base := by
  rw [M.realize_naturalStepFormula φ params members hzero hp hy hb]
  constructor
  · rintro (⟨_, equal⟩ | ⟨m, _, x, _, equal, _⟩)
    · exact equal
    · have impossible : m ∈ natSetCode 0 := equal.symm ▸ ZFSet.mem_insert m m
      exact False.elim (ZFSet.notMem_empty m impossible)
  · intro equal
    exact Or.inl ⟨rfl, equal⟩

theorem realize_naturalStep_succ {k : Nat} (φ : SetFormula (k + 2))
    (params : Fin k → ZFSet.{u}) (members : ∀ i, params i ∈ M.sets)
    (n : Nat) {p y base : ZFSet.{u}} (hn : natSetCode n ∈ M.sets)
    (hnext : natSetCode (n + 1) ∈ M.sets)
    (hp : p ∈ M.sets) (hy : y ∈ M.sets) (hb : base ∈ M.sets) :
    Realize M.sets (naturalStepFormula φ)
      (extend (natSetCode (n + 1)) (extend p (extend y (extend base params)))) ↔
      ∃ x ∈ M.sets, ZFSet.pair (natSetCode n) x ∈ p ∧
        Realize M.sets φ (extend x (extend y params)) := by
  rw [M.realize_naturalStepFormula φ params members hnext hp hy hb]
  constructor
  · rintro (⟨empty, _⟩ | ⟨m, _, x, hx, equal, entry, next⟩)
    · exact False.elim (ZFSet.notMem_empty (natSetCode n)
        (empty ▸ ZFSet.mem_insert (natSetCode n) (natSetCode n)))
    · have same := (natSetCode_succ_eq_insert_iff n m).1 equal
      exact ⟨x, hx, same ▸ entry, next⟩
  · rintro ⟨x, hx, entry, next⟩
    exact Or.inr ⟨natSetCode n, hn, x, hx, rfl, entry, next⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})
variable {k : Nat} (φ : SetFormula (k + 2)) (params : Fin k → ZFSet.{u})
variable (members : ∀ i, params i ∈ M.sets)
variable (value : Nat → ZFSet.{u}) (values : ∀ n, value n ∈ M.sets)
variable (nextValue : ∀ n y, y ∈ M.sets →
  (Realize M.sets φ (extend (value n) (extend y params)) ↔ y = value (n + 1)))

include members values nextValue

theorem definableNaturalTrace_value {N t : ZFSet.{u}} (hN : N ∈ M.sets)
    (ordinal : ordinalSetProperty N)
    (trace : OrdinalRecursionTrace
      (groundRecursionStep M (naturalStepFormula φ) (extend (value 0) params)) N t) :
    ∀ n, natSetCode n ∈ N → ∀ y, ZFSet.pair (natSetCode n) y ∈ t → y = value n := by
  intro n
  induction n with
  | zero =>
    intro hn y entry
    obtain ⟨hp, hy, relation⟩ := trace.2 _ hn y entry
    exact (M.realize_naturalStep_zero φ params members (M.transitive hN hn)
      hp hy (values 0)).1 relation
  | succ n ih =>
    intro hn y entry
    have previous : natSetCode n ∈ natSetCode (n + 1) :=
      (natSetCode_mem_iff n (n + 1)).2 (Nat.lt_succ_self n)
    have hnN := ordinal.1 _ hn _ previous
    obtain ⟨hp, hy, relation⟩ := trace.2 _ hn y entry
    obtain ⟨x, _, oldEntry, next⟩ := (M.realize_naturalStep_succ φ params members n
      (M.transitive hN hnN) (M.transitive hN hn) hp hy (values 0)).1 relation
    have equal := ih hnN x (pair_mem_graphRestriction.1 oldEntry).1
    rw [equal] at next
    exact (nextValue n y hy).1 next

theorem definableNaturalStepClosure (hω : (ZFSet.omega : ZFSet.{u}) ∈ M.sets) :
    GroundOrdinalStepClosure M ZFSet.omega (naturalStepFormula φ) (extend (value 0) params) := by
  intro a ha p hp trace
  obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode a).1 ha
  have hn (j : Nat) : natSetCode j ∈ M.sets := M.transitive hω (natSetCode_mem_omega j)
  cases n with
  | zero =>
    refine ⟨value 0, values 0,
      (M.realize_naturalStep_zero φ params members (hn 0) hp (values 0) (values 0)).2 rfl, ?_⟩
    intro y hy relation
    exact (M.realize_naturalStep_zero φ params members (hn 0) hp hy (values 0)).1 relation
  | succ n =>
    have previous : natSetCode n ∈ natSetCode (n + 1) :=
      (natSetCode_mem_iff n (n + 1)).2 (Nat.lt_succ_self n)
    have ordinal : ordinalSetProperty (natSetCode (n + 1) : ZFSet.{u}) := by
      rw [← ordinalCode_nat]
      exact ordinalSetProperty_ordinalCode _
    have entryValue := M.definableNaturalTrace_value φ params members value values nextValue
      (hn (n + 1)) ordinal trace
    obtain ⟨x, entry⟩ := trace.1.total previous
    have equal := entryValue n previous x entry
    have canonical : ZFSet.pair (natSetCode n) (value n) ∈ p := equal ▸ entry
    refine ⟨value (n + 1), values (n + 1), ?_, ?_⟩
    · exact (M.realize_naturalStep_succ φ params members n (hn n) (hn (n + 1))
        hp (values (n + 1)) (values 0)).2
          ⟨value n, values n, canonical, (nextValue n _ (values (n + 1))).2 rfl⟩
    · intro y hy relation
      obtain ⟨x, _, oldEntry, next⟩ := (M.realize_naturalStep_succ φ params members n
        (hn n) (hn (n + 1)) hp hy (values 0)).1 relation
      have same := entryValue n previous x oldEntry
      rw [same] at next
      exact (nextValue n y hy).1 next

theorem exists_definableNaturalHistory
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0) :
    ∃ history ∈ M.sets,
      OrdinalRecursionTrace
        (groundRecursionStep M (naturalStepFormula φ) (extend (value 0) params))
        ZFSet.omega history ∧
      (∀ n y, ZFSet.pair (natSetCode n) y ∈ history ↔ y = value n) ∧
      (∀ other, OrdinalRecursionTrace
        (groundRecursionStep M (naturalStepFormula φ) (extend (value 0) params))
        ZFSet.omega other → other = history) := by
  have hω := M.omega_mem separation infinite
  have ordinal : ordinalSetProperty (ZFSet.omega : ZFSet.{u}) := by
    rw [← ordinalCode_omega]
    exact ordinalSetProperty_ordinalCode Ordinal.omega0
  obtain ⟨history, hh, trace, unique, _⟩ := M.exists_unique_ordinalRecursionTrace pairing unions
    separation collection hω ordinal (naturalStepFormula φ) (extend (value 0) params)
    (Fin.cases (values 0) members)
    (M.definableNaturalStepClosure φ params members value values nextValue hω)
  refine ⟨history, hh, trace, ?_, unique⟩
  intro n y
  have hn := natSetCode_mem_omega n
  have entryValue := M.definableNaturalTrace_value φ params members value values nextValue
    hω ordinal trace
  constructor
  · exact entryValue n hn y
  · intro equal
    obtain ⟨z, entry⟩ := trace.1.total hn
    exact equal.symm ▸ (entryValue n hn z entry ▸ entry)

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem compressionStamp_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    {base : ZFSet.{u}} (hBase : base ∈ M.sets) (n : Nat) :
    compressionStamp base n ∈ M.sets := by
  induction n with
  | zero => exact M.insert_mem pairing unions hBase hBase
  | succ n ih => exact M.insert_mem pairing unions ih ih

theorem exists_groundCompressionStamps
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {base : ZFSet.{u}} (hBase : base ∈ M.sets) (ordinal : ordinalSetProperty base) :
    ∃ stamps ∈ M.sets, ∃ limit ∈ M.sets,
      limit = naturalFamilyUnion stamps ∧ CompressionStampCode base stamps limit := by
  let formula : SetFormula 2 := (BoundedFormula.successorFormula 1 0).toFormula
  have values : ∀ n, compressionStamp base n ∈ M.sets := M.compressionStamp_mem pairing unions hBase
  have nextValue : ∀ n y, y ∈ M.sets →
      (Realize M.sets formula (extend (compressionStamp base n) (extend y Fin.elim0)) ↔
        y = compressionStamp base (n + 1)) := by
    intro n y hy
    exact (BoundedFormula.realize_toFormula M (BoundedFormula.successorFormula 1 0)
      (extend (compressionStamp base n) (extend y Fin.elim0))
      (Fin.cases (values n) (Fin.cases hy (fun i => Fin.elim0 i)))).trans
        (BoundedFormula.truth_successorFormula 1 0 _)
  obtain ⟨stamps, hStamps, trace, entries, _⟩ :=
    M.exists_definableNaturalHistory formula Fin.elim0 (fun i => Fin.elim0 i)
      (compressionStamp base) values nextValue pairing unions separation collection infinite
  have valueEq (n : Nat) : trace.1.natValue n = compressionStamp base n :=
    (entries n _).1 (trace.1.natValue_entry n)
  have unionCode : NatUnionCode (compressionStamp base) (naturalFamilyUnion stamps) := by
    intro x
    simpa only [valueEq] using (naturalFamilyUnion_code trace.1 x)
  have stampBelow (n : Nat) : compressionStamp base n ∈ naturalFamilyUnion stamps :=
    unionCode.subset (n + 1) (ZFSet.mem_insert _ _)
  refine ⟨stamps, hStamps, naturalFamilyUnion stamps,
    M.naturalFamilyUnion_mem unions separation (M.omega_mem separation infinite) hStamps, rfl,
    ⟨⟨?_, ?_⟩, entries, unionCode, compressionStamp_union_ordinal ordinal unionCode⟩⟩
  · intro z hz
    obtain ⟨i, hi, y, rfl⟩ := trace.1.shape z hz
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode i).1 hi
    exact ZFSet.pair_mem_prod.2 ⟨natSetCode_mem_omega n, (entries n y).1 hz ▸ stampBelow n⟩
  · obtain ⟨_, function⟩ := trace.1
    exact function.2

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

namespace CompressionStampCode
variable {base stamps limit K : ZFSet.{u}} (code : CompressionStampCode base stamps limit)
include code

theorem function_into_bound (values : ∀ n, compressionStamp base n ∈ K) :
    ZFSet.IsFunc ZFSet.omega K stamps := by
  refine ⟨?_, code.function.2⟩
  intro z hz
  obtain ⟨x, hx, y, _, rfl⟩ := ZFSet.mem_prod.1 (code.function.1 hz)
  obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode x).1 hx
  exact ZFSet.pair_mem_prod.2 ⟨natSetCode_mem_omega n, (code.entries n y).1 hz ▸ values n⟩

theorem successor_mem_limit {a : ZFSet.{u}} (ha : a ∈ limit) : insert a a ∈ limit := by
  obtain ⟨n, member⟩ := (code.union a).1 ha
  rw [ordinalSetProperty_eq_code_rank a (ordinalSetProperty_member code.ordinal ha),
    ← ordinalCode_succ, ordinalSetProperty_eq_code_rank limit code.ordinal, mem_ordinalCode_iff]
  exact (Order.succ_le_iff.2 (ZFSet.rank_lt_of_mem member)).trans_lt
    (ZFSet.rank_lt_of_mem (code.stamp_mem_limit n))

theorem rank_isLimit : Order.IsSuccLimit (ZFSet.rank limit) := by
  apply Order.isSuccLimit_iff_of_orderBot.2
  refine ⟨ne_of_gt (bot_le.trans_lt (ZFSet.rank_lt_of_mem code.base_mem_limit)), ?_⟩
  rw [Order.isSuccPrelimit_iff_succ_lt]
  intro a ha
  have member : ordinalCode a ∈ limit := by
    rw [ordinalSetProperty_eq_code_rank limit code.ordinal, mem_ordinalCode_iff]
    exact ha
  have bound := ZFSet.rank_lt_of_mem (code.successor_mem_limit member)
  rw [← ordinalCode_succ, rank_ordinalCode] at bound
  exact bound

end CompressionStampCode

namespace GroundInaccessibleConditions
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}
variable (conditions : GroundInaccessibleConditions M K)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hK : K ∈ M.sets)
include conditions pairing unions powers separation infinite hK

theorem compressionStamp_mem {base : ZFSet.{u}} (hBase : base ∈ K) (n : Nat) :
    compressionStamp base n ∈ K := by
  induction n with
  | zero => exact conditions.successor_mem pairing unions powers separation infinite hK hBase
  | succ n ih => exact conditions.successor_mem pairing unions powers separation infinite hK ih

theorem compressionStamp_limit_mem {base stamps limit : ZFSet.{u}}
    (code : CompressionStampCode base stamps limit) (hBase : base ∈ K)
    (hStamps : stamps ∈ M.sets) : limit ∈ K := by
  have values := conditions.compressionStamp_mem pairing unions powers separation infinite hK hBase
  obtain ⟨δ, hδ, bounded⟩ := conditions.2.2.1 ZFSet.omega conditions.2.1 stamps hStamps
    (code.function_into_bound values)
  have subset : limit ⊆ δ := by
    intro x hx
    obtain ⟨n, member⟩ := (code.union x).1 hx
    exact (ordinalSetProperty_member conditions.1 hδ).1 (compressionStamp base n)
      (bounded _ _ ((code.entries n _).2 rfl)) x member
  obtain ⟨l, eqLimit⟩ := (ordinalSetProperty_iff limit).1 code.ordinal
  obtain ⟨d, eqDelta⟩ := (ordinalSetProperty_iff δ).1 (ordinalSetProperty_member conditions.1 hδ)
  obtain ⟨k, eqK⟩ := (ordinalSetProperty_iff K).1 conditions.1
  rw [eqLimit, eqDelta, ordinalCode_subset_iff] at subset
  rw [eqDelta, eqK, mem_ordinalCode_iff] at hδ
  rw [eqLimit, eqK, mem_ordinalCode_iff]
  exact subset.trans_lt hδ

end GroundInaccessibleConditions

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem exists_groundCompressionStamps_below
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    {K base : ZFSet.{u}} (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    (hBase : base ∈ K) :
    ∃ stamps ∈ M.sets, ∃ limit ∈ M.sets,
      limit = naturalFamilyUnion stamps ∧ CompressionStampCode base stamps limit ∧
        limit ∈ K ∧ Order.IsSuccLimit (ZFSet.rank limit) ∧ base ∈ limit := by
  obtain ⟨stamps, hStamps, limit, hLimit, equal, code⟩ :=
    M.exists_groundCompressionStamps pairing unions separation collection infinite
      (M.transitive hK hBase) (ordinalSetProperty_member conditions.1 hBase)
  exact ⟨stamps, hStamps, limit, hLimit, equal, code,
    conditions.compressionStamp_limit_mem pairing unions powers separation infinite hK code hBase hStamps,
    code.rank_isLimit, code.base_mem_limit⟩

end TransitiveGround
end PartitionPilot.Forcing

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundEligibleCaps
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetRealization
universe u

theorem literalTaskBound_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    {P R U Labels : ZFSet.{u}} (points : ZFSet.rank P < o) (relations : ZFSet.rank R < o)
    (filters : ZFSet.rank U < o) (labels : ZFSet.rank Labels < o) :
    ZFSet.rank (literalTaskBound P R U Labels) < o :=
  rank_product_lt limit points (rank_product_lt limit points
    (rank_product_lt limit relations (rank_product_lt limit points (rank_product_lt limit filters labels))))

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

theorem groundMeetFilters_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    {P : ZFSet.{u}} (r μ : ZFSet.{u}) (points : ZFSet.rank P < o) :
    ZFSet.rank (M.groundMeetFilters P r μ) < o :=
  (ZFSet.rank_mono (show M.groundMeetFilters P r μ ⊆ M.groundPower P
    from fun _ hz => (ZFSet.mem_sep.1 hz).1)).trans_lt (M.groundPower_rank_lt limit points)

theorem groundEligibleTasks_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    {P Labels : ZFSet.{u}} (G r μ A : ZFSet.{u})
    (points : ZFSet.rank P < o) (labels : ZFSet.rank Labels < o) :
    ZFSet.rank (M.groundEligibleTasks P G r μ A Labels) < o :=
  (ZFSet.rank_mono (eligibleTaskSet_subset P G r μ A (M.groundRelations P P)
    (M.groundMeetFilters P r μ) Labels)).trans_lt
      (literalTaskBound_rank_lt limit points (M.groundRelations_rank_lt limit points points)
        (M.groundMeetFilters_rank_lt limit r μ points) labels)

end TransitiveGround

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_RecursiveStateFieldEnvironments
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing

universe u

namespace RecursiveStateData

theorem field_injective : Function.Injective field.{u} := by
  intro first second equal
  cases first
  cases second
  congr 1
  · exact congrFun equal (0 : Fin 13)
  · exact congrFun equal (1 : Fin 13)
  · exact congrFun equal (2 : Fin 13)
  · exact congrFun equal (3 : Fin 13)
  · exact congrFun equal (4 : Fin 13)
  · exact congrFun equal (5 : Fin 13)
  · exact congrFun equal (6 : Fin 13)
  · exact congrFun equal (7 : Fin 13)
  · exact congrFun equal (8 : Fin 13)
  · exact congrFun equal (9 : Fin 13)
  · exact congrFun equal (10 : Fin 13)
  · exact congrFun equal (11 : Fin 13)
  · exact congrFun equal (12 : Fin 13)

theorem code_injective : Function.Injective code.{u} := by
  intro first second equal
  exact field_injective (nonemptyTupleCode_injective 12 equal)

end RecursiveStateData

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem recursiveStateData_code_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (state : RecursiveStateData.{u}) (ground : ∀ j, state.field j ∈ M.sets) :
    state.code ∈ M.sets := M.nonemptyTupleCode_mem pairing 12 state.field ground

theorem recursiveStateData_field_mem (state : RecursiveStateData.{u})
    (ground : state.code ∈ M.sets) : ∀ j, state.field j ∈ M.sets :=
  M.nonemptyTupleCode_field_mem 12 state.field ground

theorem recursiveStateCode_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {D rD μD J Qs rs μs As Es Fs Ss Maps A : ZFSet.{u}}
    (hD : D ∈ M.sets)
    (hrD : rD ∈ M.sets)
    (hμD : μD ∈ M.sets)
    (hJ : J ∈ M.sets)
    (hQs : Qs ∈ M.sets)
    (hrs : rs ∈ M.sets)
    (hμs : μs ∈ M.sets)
    (hAs : As ∈ M.sets)
    (hEs : Es ∈ M.sets)
    (hFs : Fs ∈ M.sets)
    (hSs : Ss ∈ M.sets)
    (hMaps : Maps ∈ M.sets)
    (hA : A ∈ M.sets)
    : recursiveStateCode D rD μD J Qs rs μs As Es Fs Ss Maps A ∈ M.sets :=
  M.recursiveStateData_code_mem pairing ⟨D, rD, μD, J, Qs, rs, μs, As, Es, Fs, Ss, Maps, A⟩
    (Fin.cases hD (Fin.cases hrD (Fin.cases hμD (Fin.cases hJ (Fin.cases hQs (Fin.cases hrs (Fin.cases hμs (Fin.cases hAs (Fin.cases hEs (Fin.cases hFs (Fin.cases hSs (Fin.cases hMaps (Fin.cases hA ((fun i => Fin.elim0 i)))))))))))))))

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.RecursiveStateData
universe u

theorem ofFields_field (state : RecursiveStateData.{u}) : ofFields state.field = state := by
  cases state
  rfl

theorem field_ofFields (fields : Fin 13 → ZFSet.{u}) : (ofFields fields).field = fields := by
  funext j
  refine Fin.cases rfl (fun j => ?_) j
  refine Fin.cases rfl (fun j => ?_) j
  refine Fin.cases rfl (fun j => ?_) j
  refine Fin.cases rfl (fun j => ?_) j
  refine Fin.cases rfl (fun j => ?_) j
  refine Fin.cases rfl (fun j => ?_) j
  refine Fin.cases rfl (fun j => ?_) j
  refine Fin.cases rfl (fun j => ?_) j
  refine Fin.cases rfl (fun j => ?_) j
  refine Fin.cases rfl (fun j => ?_) j
  refine Fin.cases rfl (fun j => ?_) j
  refine Fin.cases rfl (fun j => ?_) j
  refine Fin.cases rfl (fun j => ?_) j
  exact Fin.elim0 j

theorem code_ofFields (fields : Fin 13 → ZFSet.{u}) :
    (ofFields fields).code = nonemptyTupleCode 12 fields := by
  rw [code, field_ofFields]

theorem successorCodeFromEnvironment_spec (state : RecursiveStateData.{u})
    (M : TransitiveGround.{u}) (I Sources Reps G T : ZFSet.{u}) :
    successorCodeFromEnvironment M (state.successorEnvironment I Sources Reps G T) =
      (state.successor M I Sources Reps G T).code := by
  simp only [successorCodeFromEnvironment, successorEnvironment, Fin.addCases_left]
  rw [ofFields_field]
  rfl

end PartitionPilot.Forcing.RecursiveStateData

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_InitialCompressionAccounting
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

namespace GroundCompressionState
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)

theorem code_mem (pairing : Realize M.sets SetFormula.pairing Fin.elim0) :
    state.data.code ∈ M.sets := by
  rw [← state.inputs_toState]
  exact M.recursiveStateCode_mem pairing state.ground.carrier state.ground.order
    state.ground.meet state.ground.indices state.ground.spaces state.ground.relations
    state.ground.meets state.ground.anchors state.ground.embeddings state.ground.filters
    state.ground.separators state.ground.maps state.ground.action

end GroundCompressionState

end

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundInitialCompressionHistory
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

namespace GroundCompressionState
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets)

include pairing unions powers separation hI hSources hReps hG hT in
theorem canonical_iterate_code_mem (n : Nat) :
    (state.data.iterate M I Sources Reps G T n).code ∈ M.sets := by
  rw [← state.iterate_data pairing unions powers separation hI hSources hReps hG hT n]
  exact (state.iterate pairing unions powers separation hI hSources hReps hG hT n).code_mem pairing

end GroundCompressionState
end PartitionPilot.Forcing

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_decodedSuccessorFormula
    (definition : GroundDefinableFunction M (RecursiveStateData.successorCodeFromEnvironment M))
    (params : Fin 5 → ZFSet.{u}) (members : ∀ i, params i ∈ M.sets)
    {x y : ZFSet.{u}} (hx : x ∈ M.sets) (hy : y ∈ M.sets) :
    Realize M.sets (decodedSuccessorFormula definition.formula) (extend x (extend y params)) ↔
      ∃ fields : Fin 13 → ZFSet.{u}, (∀ i, fields i ∈ M.sets) ∧
        x = nonemptyTupleCode 12 fields ∧
        y = RecursiveStateData.successorCodeFromEnvironment M
          (Fin.addCases (m := 13) (n := 5) fields params) := by
  rw [decodedSuccessorFormula, realize_exBlock]
  apply exists_congr
  intro fields
  apply and_congr_right
  intro hfields
  have henv : ∀ i, extendMany 13 fields (extend x (extend y params)) i ∈ M.sets :=
    extendMany_members 13 fields _ hfields (Fin.cases hx (Fin.cases hy members))
  change (Realize M.sets (BoundedFormula.nonemptyTupleFormula 12
      (suffixIndex 7 13 0) (prefixIndex 7 13)).toFormula _ ∧ _) ↔ _
  rw [BoundedFormula.realize_toFormula M _ _ henv, BoundedFormula.truth_nonemptyTupleFormula,
    realize_reindex, map_extend]
  have fieldsEqual : (fun i => extendMany 13 fields (extend x (extend y params))
      (prefixIndex 7 13 i)) = fields := by
    funext i
    exact extendMany_prefix 13 fields _ i
  have envEqual : (fun i => extendMany 13 fields (extend x (extend y params))
      (Fin.addCases (m := 13) (n := 5) (prefixIndex 7 13)
        (fun j => suffixIndex 7 13 j.succ.succ) i)) =
      Fin.addCases (m := 13) (n := 5) fields params := by
    funext i
    refine Fin.addCases (m := 13) (n := 5) (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.addCases_left]
      exact extendMany_prefix 13 fields _ j
    · simp only [Fin.addCases_right]
      exact extendMany_suffix 13 fields _ j.succ.succ
  rw [fieldsEqual, envEqual, extendMany_suffix, extendMany_suffix]
  change (x = nonemptyTupleCode 12 fields ∧
    Realize M.sets definition.formula
      (extend y (Fin.addCases (m := 13) (n := 5) fields params))) ↔ _
  rw [definition.correct _ (fun i =>
    Fin.addCases (m := 13) (n := 5)
      (fun j => by simpa only [Fin.addCases_left] using hfields j)
      (fun j => by simpa only [Fin.addCases_right] using members j) i) y hy]

theorem realize_recursiveSuccessorCode
    (definition : GroundDefinableFunction M (RecursiveStateData.successorCodeFromEnvironment M))
    (state : RecursiveStateData.{u}) (hstate : state.code ∈ M.sets)
    {I Sources Reps G T y : ZFSet.{u}}
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets) (hy : y ∈ M.sets) :
    Realize M.sets (decodedSuccessorFormula definition.formula)
      (extend state.code (extend y (extend I (extend Sources
        (extend Reps (extend G (extend T Fin.elim0))))))) ↔
      y = (state.successor M I Sources Reps G T).code := by
  rw [M.realize_decodedSuccessorFormula definition _
    (Fin.cases hI (Fin.cases hSources (Fin.cases hReps (Fin.cases hG (Fin.cases hT
      (fun i => Fin.elim0 i)))))) hstate hy]
  constructor
  · rintro ⟨fields, _, code, next⟩
    have equal : RecursiveStateData.ofFields fields = state :=
      RecursiveStateData.code_injective ((RecursiveStateData.code_ofFields fields).trans code.symm)
    have fieldsEqual : fields = state.field := by
      rw [← RecursiveStateData.field_ofFields fields, equal]
    rw [fieldsEqual] at next
    exact next.trans (state.successorCodeFromEnvironment_spec M I Sources Reps G T)
  · intro next
    refine ⟨state.field, M.recursiveStateData_field_mem state hstate, rfl, ?_⟩
    exact next.trans (state.successorCodeFromEnvironment_spec M I Sources Reps G T).symm

end TransitiveGround
end PartitionPilot.Forcing

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace GroundCompressionState
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)

theorem exists_groundHistory
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets) :
    let φ := M.compressionSuccessorFormula pairing unions powers separation
    let params := extend state.data.code
      (extend I (extend Sources (extend Reps (extend G (extend T Fin.elim0)))))
    ∃ history ∈ M.sets,
      OrdinalRecursionTrace (groundRecursionStep M (naturalStepFormula φ) params) ZFSet.omega history ∧
      (∀ n y, ZFSet.pair (natSetCode n) y ∈ history ↔
        y = (state.data.iterate M I Sources Reps G T n).code) ∧
      (∀ other, OrdinalRecursionTrace (groundRecursionStep M (naturalStepFormula φ) params)
        ZFSet.omega other → other = history) ∧
      ∀ n, ∃ current : GroundCompressionState M seed,
        current.data = state.data.iterate M I Sources Reps G T n := by
  dsimp only
  let φ := M.compressionSuccessorFormula pairing unions powers separation
  let params := extend I (extend Sources (extend Reps (extend G (extend T Fin.elim0))))
  have members : ∀ i, params i ∈ M.sets :=
    Fin.cases hI (Fin.cases hSources (Fin.cases hReps (Fin.cases hG
      (Fin.cases hT (fun i => Fin.elim0 i)))))
  let value (n : Nat) := (state.data.iterate M I Sources Reps G T n).code
  have values : ∀ n, value n ∈ M.sets :=
    state.canonical_iterate_code_mem pairing unions powers separation hI hSources hReps hG hT
  have nextValue : ∀ n y, y ∈ M.sets →
      (Realize M.sets φ (extend (value n) (extend y params)) ↔ y = value (n + 1)) := by
    intro n y hy
    exact M.realize_recursiveSuccessorCode
      (M.definable_recursiveSuccessorCode pairing unions powers separation)
      (state.data.iterate M I Sources Reps G T n) (values n) hI hSources hReps hG hT hy
  obtain ⟨history, hh, trace, entries, unique⟩ :=
    M.exists_definableNaturalHistory φ params members value values nextValue
      pairing unions separation collection infinite
  exact ⟨history, hh, trace, entries, unique,
    state.canonical_iterate_valid pairing unions powers separation hI hSources hReps hG hT⟩

end GroundCompressionState
end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_HistoryFieldFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})

theorem realize_stateFieldFormula {n} (code value : Fin n) (j : Fin 13)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (state : RecursiveStateData.{u}) (coded : env code = state.code) :
    Realize M.sets (stateFieldFormula code value j) env ↔ env value = state.field j := by
  rw [stateFieldFormula, realize_exBlock]
  constructor
  · rintro ⟨fields, fieldMembers, tuple, entry⟩
    have equal := (BoundedFormula.truth_nonemptyTupleFormula 12 (suffixIndex n 13 code)
      (prefixIndex n 13) _).1
      ((BoundedFormula.realize_toFormula M _ _ (extendMany_members 13 fields env fieldMembers members)).1 tuple)
    simp only [extendMany_suffix, extendMany_prefix] at equal
    have fieldsEqual : fields = state.field :=
      nonemptyTupleCode_injective 12 (equal.symm.trans coded)
    change extendMany 13 fields env (suffixIndex n 13 value) =
      extendMany 13 fields env (prefixIndex n 13 j) at entry
    simpa only [extendMany_suffix, extendMany_prefix, fieldsEqual] using entry
  · intro equal
    have fieldMembers := M.recursiveStateData_field_mem state (coded ▸ members code)
    refine ⟨state.field, fieldMembers, ?_, ?_⟩
    · apply (BoundedFormula.realize_toFormula M _ _
        (extendMany_members 13 state.field env fieldMembers members)).2
      apply (BoundedFormula.truth_nonemptyTupleFormula 12 (suffixIndex n 13 code)
        (prefixIndex n 13) _).2
      simp only [extendMany_suffix, extendMany_prefix]
      exact coded
    · change extendMany 13 state.field env (suffixIndex n 13 value) =
        extendMany 13 state.field env (prefixIndex n 13 j)
      simpa only [extendMany_suffix, extendMany_prefix] using equal

theorem realize_historyFieldValueFormula {k} (index value history : Fin k) (j : Fin 13)
    (env : Fin k → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (states : Nat → RecursiveStateData.{u})
    (entries : ∀ n y, ZFSet.pair (natSetCode n) y ∈ env history ↔ y = (states n).code)
    (n : Nat) (indexEq : env index = natSetCode n) :
    Realize M.sets (historyFieldValueFormula index value history j) env ↔
      env value = (states n).field j := by
  rw [historyFieldValueFormula, realize_ex]
  constructor
  · rintro ⟨code, hcode, entry, projected⟩
    have extended : ∀ i, extend code env i ∈ M.sets := Fin.cases hcode members
    have actual := (BoundedFormula.truth_pairMembershipFormula index.succ 0 history.succ _).1
      ((BoundedFormula.realize_toFormula M _ _ extended).1 entry)
    change ZFSet.pair (env index) code ∈ env history at actual
    rw [indexEq] at actual
    exact (M.realize_stateFieldFormula 0 value.succ j (extend code env) extended
      (states n) ((entries n code).1 actual)).1 projected
  · intro equal
    have entry : ZFSet.pair (natSetCode n) (states n).code ∈ env history :=
      (entries n _).2 rfl
    have hcode := M.pair_right (M.transitive (members history) entry)
    have extended : ∀ i, extend (states n).code env i ∈ M.sets := Fin.cases hcode members
    refine ⟨(states n).code, hcode, ?_, ?_⟩
    · apply (BoundedFormula.realize_toFormula M _ _ extended).2
      apply (BoundedFormula.truth_pairMembershipFormula index.succ 0 history.succ _).2
      change ZFSet.pair (env index) (states n).code ∈ env history
      exact indexEq.symm ▸ entry
    · exact (M.realize_stateFieldFormula 0 value.succ j _ extended (states n) rfl).2 equal

theorem realize_historyFieldPairFormula {k} (index output history : Fin k) (j : Fin 13)
    (env : Fin k → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (states : Nat → RecursiveStateData.{u})
    (entries : ∀ n y, ZFSet.pair (natSetCode n) y ∈ env history ↔ y = (states n).code)
    (n : Nat) (indexEq : env index = natSetCode n) :
    Realize M.sets (historyFieldPairFormula index output history j) env ↔
      env output = ZFSet.pair (natSetCode n) ((states n).field j) := by
  rw [historyFieldPairFormula, realize_ex]
  constructor
  · rintro ⟨value, hvalue, specified, pair⟩
    have extended : ∀ i, extend value env i ∈ M.sets := Fin.cases hvalue members
    have valueEq := (M.realize_historyFieldValueFormula index.succ 0 history.succ j
      (extend value env) extended states entries n indexEq).1 specified
    have pairEq := (BoundedFormula.truth_orderedPairFormula output.succ index.succ 0 _).1
      ((BoundedFormula.realize_toFormula M _ _ extended).1 pair)
    change env output = ZFSet.pair (env index) value at pairEq
    exact pairEq.trans (congrArg₂ ZFSet.pair indexEq valueEq)
  · intro equal
    have codeM := M.pair_right (M.transitive (members history) ((entries n _).2 rfl))
    have valueM := M.recursiveStateData_field_mem (states n) codeM j
    have extended : ∀ i, extend ((states n).field j) env i ∈ M.sets := Fin.cases valueM members
    refine ⟨(states n).field j, valueM, ?_, ?_⟩
    · exact (M.realize_historyFieldValueFormula index.succ 0 history.succ j _ extended
        states entries n indexEq).2 rfl
    · apply (BoundedFormula.realize_toFormula M _ _ extended).2
      apply (BoundedFormula.truth_orderedPairFormula output.succ index.succ 0 _).2
      change env output = ZFSet.pair (env index) ((states n).field j)
      exact equal.trans (congrArg (fun x => ZFSet.pair x ((states n).field j)) indexEq.symm)

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundHistoryFields
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem exists_groundStateFieldFamily
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (hω : (ZFSet.omega : ZFSet.{u}) ∈ M.sets)
    {history : ZFSet.{u}} (hHistory : history ∈ M.sets)
    (states : Nat → RecursiveStateData.{u})
    (entries : ∀ n y, ZFSet.pair (natSetCode n) y ∈ history ↔ y = (states n).code)
    (j : Fin 13) :
    ∃ family ∈ M.sets, FunctionGraphOn ZFSet.omega family ∧
      ∀ n y, ZFSet.pair (natSetCode n) y ∈ family ↔ y = (states n).field j := by
  let params := extend history Fin.elim0
  have paramsM : ∀ i, params i ∈ M.sets := Fin.cases hHistory (fun i => Fin.elim0 i)
  have fieldsM (n : Nat) : (states n).field j ∈ M.sets :=
    M.recursiveStateData_field_mem (states n)
      (M.pair_right (M.transitive hHistory ((entries n _).2 rfl))) j
  have naturalM (n : Nat) : natSetCode n ∈ M.sets := M.transitive hω (natSetCode_mem_omega n)
  have total : ∀ x ∈ M.sets, x ∈ ZFSet.omega → ∃ z ∈ M.sets,
      Realize M.sets (historyFieldPairFormula 0 1 2 j) (extend x (extend z params)) ∧
      ∀ w ∈ M.sets,
        Realize M.sets (historyFieldPairFormula 0 1 2 j) (extend x (extend w params)) → w = z := by
    intro x hx hxω
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode x).1 hxω
    have pairM := M.orderedPair_mem pairing hx (fieldsM n)
    refine ⟨ZFSet.pair (natSetCode n) ((states n).field j), pairM, ?_, ?_⟩
    · exact (M.realize_historyFieldPairFormula 0 1 2 j _
        (Fin.cases hx (Fin.cases pairM paramsM)) states entries n rfl).2 rfl
    · intro w hw specified
      exact (M.realize_historyFieldPairFormula 0 1 2 j _
        (Fin.cases hx (Fin.cases hw paramsM)) states entries n rfl).1 specified
  obtain ⟨family, hFamily, image⟩ := replacement_of_collection_separation M.sets collection separation
    (historyFieldPairFormula 0 1 2 j) params paramsM ZFSet.omega hω total
  have allEntries (z : ZFSet.{u}) :
      z ∈ family ↔ ∃ n, z = ZFSet.pair (natSetCode n) ((states n).field j) := by
    constructor
    · intro member
      have hz := M.transitive hFamily member
      obtain ⟨x, hx, hxω, specified⟩ := (image z hz).1 member
      obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode x).1 hxω
      exact ⟨n, (M.realize_historyFieldPairFormula 0 1 2 j _
        (Fin.cases hx (Fin.cases hz paramsM)) states entries n rfl).1 specified⟩
    · rintro ⟨n, rfl⟩
      have pairM := M.orderedPair_mem pairing (naturalM n) (fieldsM n)
      apply (image _ pairM).2
      exact ⟨natSetCode n, naturalM n, natSetCode_mem_omega n,
        (M.realize_historyFieldPairFormula 0 1 2 j _
          (Fin.cases (naturalM n) (Fin.cases pairM paramsM)) states entries n rfl).2 rfl⟩
  have exactEntries (n : Nat) (y : ZFSet.{u}) :
      ZFSet.pair (natSetCode n) y ∈ family ↔ y = (states n).field j := by
    rw [allEntries]
    constructor
    · rintro ⟨m, equal⟩
      obtain ⟨index, value⟩ := ZFSet.pair_inj.1 equal
      have same : n = m := natSetCode_injective index
      exact same ▸ value
    · intro equal
      exact ⟨n, congrArg (ZFSet.pair (natSetCode n)) equal⟩
  refine ⟨family, hFamily, ⟨⋃₀ ⋃₀ family, ?_, ?_⟩, exactEntries⟩
  · intro z member
    obtain ⟨n, rfl⟩ := (allEntries z).1 member
    exact ZFSet.pair_mem_prod.2 ⟨natSetCode_mem_omega n, pair_second_mem_doubleUnion member⟩
  · intro x hx
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode x).1 hx
    refine ⟨(states n).field j, (exactEntries n _).2 rfl, ?_⟩
    intro y hy
    exact (exactEntries n y).1 hy

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundCompressionOrigins
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetRealization
universe u

theorem rank_taggedExtension_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    {P N : ZFSet.{u}} (points : ZFSet.rank P < o) (fresh : ZFSet.rank N < o) :
    ZFSet.rank (taggedExtension P N) < o := by
  rw [taggedExtension, ZFSet.rank_union]
  exact max_lt points (rank_product_lt limit (rank_singleton_lt limit points) fresh)

namespace RecursiveTemplateConstancy
variable {P r μ : ZFSet.{u}} {initial : RecursiveStateData.{u}}
variable (constant : RecursiveTemplateConstancy P r μ initial)
include constant

theorem fresh_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (indices : ZFSet.rank initial.J < o) (templates : ZFSet.rank P < o) :
    ZFSet.rank initial.fresh < o := by
  have subset : initial.fresh ⊆ ZFSet.prod initial.J P := by
    intro z hz
    have domain := indexedAttachmentFresh_subset initial.J initial.Qs initial.rs initial.As hz
    obtain ⟨i, hi, q, rfl, Q, entry, hq⟩ := (mem_indexedAttachmentDomain _ _ _).1 domain
    exact ZFSet.pair_mem_prod.2 ⟨hi, (constant.space_entry_iff i Q).1 entry |>.2 ▸ hq⟩
  exact (ZFSet.rank_mono subset).trans_lt (rank_product_lt limit indices templates)

theorem currentCarrier_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (points : ZFSet.rank initial.D < o) (indices : ZFSet.rank initial.J < o)
    (templates : ZFSet.rank P < o) : ZFSet.rank initial.currentCarrier < o :=
  rank_taggedExtension_lt limit points (constant.fresh_rank_lt limit indices templates)

theorem iterate_carrier_ranks (M : TransitiveGround.{u}) (I Sources Reps G T : ZFSet.{u})
    {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (points : ZFSet.rank initial.D < o) (indices : ZFSet.rank initial.J < o)
    (templates : ZFSet.rank P < o) (tasks : ZFSet.rank I < o) (n : Nat) :
    ZFSet.rank (initial.iterate M I Sources Reps G T n).D < o ∧
      ZFSet.rank (initial.iterate M I Sources Reps G T n).J < o := by
  induction n with
  | zero => exact ⟨points, indices⟩
  | succ n ih =>
    rw [RecursiveStateData.iterate_succ]
    refine ⟨(constant.iterate M I Sources Reps G T n).currentCarrier_rank_lt limit ih.1 ih.2 templates, ?_⟩
    exact (ZFSet.rank_mono (recursiveAttachmentIndices_subset _ _ _ _ _ _)).trans_lt
      (rank_product_lt limit tasks ih.2)

end RecursiveTemplateConstancy

theorem NatUnionCode.rank_le {sets : Nat → ZFSet.{u}} {U : ZFSet.{u}} (code : NatUnionCode sets U)
    {o : Ordinal.{u}} (bounds : ∀ n, ZFSet.rank (sets n) < o) : ZFSet.rank U ≤ o := by
  apply ZFSet.rank_le_iff.2
  intro x hx
  obtain ⟨n, member⟩ := (code x).1 hx
  exact (ZFSet.rank_lt_of_mem member).trans (bounds n)

namespace GroundCompressionUnionData
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T : ZFSet.{u}}
variable (data : GroundCompressionUnionData M initial I Sources Reps G m one T)

theorem carrier_rank_le {P r μ : ZFSet.{u}} (constant : RecursiveTemplateConstancy P r μ initial)
    {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (points : ZFSet.rank initial.D < o) (indices : ZFSet.rank initial.J < o)
    (templates : ZFSet.rank P < o) (tasks : ZFSet.rank I < o) :
    ZFSet.rank (data.fields 0) ≤ o :=
  (data.fieldUnion 0).rank_le
    (fun n => (constant.iterate_carrier_ranks M I Sources Reps G T limit points indices templates tasks n).1)

end GroundCompressionUnionData

end PartitionPilot.Forcing



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



namespace PartitionPilot.Forcing.GroundSerializedChronology
universe u
variable {M : TransitiveGround.{u}} {T T' C D rD : ZFSet.{u}}
variable (serial : GroundSerializedChronology M T C D rD)

theorem castTime_code (equal : T = T') : (serial.castTime equal).code = serial.code := by
  cases equal
  rfl

theorem castTime_value (equal : T = T') (j : Fin 5) (s : ZFSet.{u}) :
    (serial.castTime equal).fields.value j s = serial.fields.value j s := by
  cases equal
  rfl

end PartitionPilot.Forcing.GroundSerializedChronology

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



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundInitialCompressionOrigin
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
universe u
variable (M : TransitiveGround.{u})

theorem initialCompressionData_template_constancy (P G r μ A Labels : ZFSet.{u}) :
    RecursiveTemplateConstancy P r μ (M.initialCompressionData P G r μ A Labels) :=
  ⟨rfl, rfl, rfl⟩

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundInitialExternalGroup
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace TransitiveGround

open SetRealization
universe u
variable (M : TransitiveGround.{u})

theorem finiteWords_subset_powerset (A : ZFSet.{u}) :
    M.finiteWords A ⊆ ZFSet.powerset (ZFSet.prod ZFSet.omega A) := by
  intro f hf
  have relation := (ZFSet.mem_sep.1 hf).1
  exact ZFSet.mem_powerset.2 ((M.mem_groundRelations ZFSet.omega A f).1 relation).2

theorem finiteWords_rank_le (A : ZFSet.{u}) :
    ZFSet.rank (M.finiteWords A) ≤ Order.succ (ZFSet.rank (ZFSet.prod ZFSet.omega A)) := by
  have bound := ZFSet.rank_mono (M.finiteWords_subset_powerset A)
  rwa [ZFSet.rank_powerset] at bound

theorem finiteWords_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o) {A : ZFSet.{u}}
    (omega : ZFSet.rank ZFSet.omega < o) (alphabet : ZFSet.rank A < o) :
    ZFSet.rank (M.finiteWords A) < o :=
  (M.finiteWords_rank_le A).trans_lt (limit.succ_lt (rank_product_lt limit omega alphabet))

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_ExternalSlotCopyGraphs
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

theorem triple_mem_externalSlotCopyGraph (V E I U B action images j v u y : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair v u) y ∈ externalSlotCopyGraph V E I U B action images j ↔
      v ∈ V ∧ u ∈ U ∧ y ∈ B ∧ ∃ w ∈ E, ∃ r ∈ I, ∃ x ∈ B,
        v = ZFSet.pair (natSetCode 1) (ZFSet.pair w r) ∧
          ZFSet.pair (ZFSet.pair (ZFSet.pair r j) u) x ∈ images ∧
          ZFSet.pair (ZFSet.pair w x) y ∈ action := by
  rw [externalSlotCopyGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, v', hv, u', hu, y', hy, w, hw, r, hr, x, hx, equal, rest⟩
    obtain ⟨left, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 left
    exact ⟨hv, hu, hy, w, hw, r, hr, x, hx, rest⟩
  · rintro ⟨hv, hu, hy, w, hw, r, hr, x, hx, rest⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hv, hu⟩, hy⟩,
      v, hv, u, hu, y, hy, w, hw, r, hr, x, hx, rfl, rest⟩

namespace BoundedFormula

theorem truth_externalSlotCopyEntryFormula {n} (z V E I U B action images j one : Fin n)
    (env : Fin n → ZFSet.{u}) (oneEq : env one = natSetCode 1) :
    Truth (externalSlotCopyEntryFormula z V E I U B action images j one) env ↔
      env z ∈ externalSlotCopyGraph (env V) (env E) (env I) (env U) (env B)
        (env action) (env images) (env j) := by
  simp only [externalSlotCopyEntryFormula, truth_exMem, Truth, truth_orderedTripleFormula,
    truth_orderedRightTripleFormula, truth_slotImageMembershipFormula, truth_tripleMembershipFormula]
  simp only [extend, Fin.cases_zero, Fin.cases_succ]
  rw [oneEq, externalSlotCopyGraph, ZFSet.mem_sep]
  refine ⟨fun h => ⟨?_, h⟩, And.right⟩
  obtain ⟨v, hv, u, hu, y, hy, _, _, _, _, _, _, equal, _⟩ := h
  rw [equal]
  exact ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hv, hu⟩, hy⟩
end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem externalSlotCopyGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {V E I U B action images j : ZFSet.{u}}
    (hV : V ∈ M.sets) (hE : E ∈ M.sets) (hI : I ∈ M.sets) (hU : U ∈ M.sets)
    (hB : B ∈ M.sets) (hAction : action ∈ M.sets) (hImages : images ∈ M.sets) (hj : j ∈ M.sets) :
    externalSlotCopyGraph V E I U B action images j ∈ M.sets := by
  have zero := M.empty_mem ⟨U, hU⟩
  have one : natSetCode 1 ∈ M.sets := M.insert_mem pairing unions zero zero
  let params := extend V (extend E (extend I (extend U (extend B (extend action
    (extend images (extend j (extend (natSetCode 1) Fin.elim0))))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.externalSlotCopyEntryFormula 0 1 2 3 4 5 6 7 8 9) params
    (Fin.cases hV (Fin.cases hE (Fin.cases hI (Fin.cases hU (Fin.cases hB
      (Fin.cases hAction (Fin.cases hImages (Fin.cases hj (Fin.cases one (fun i => Fin.elim0 i))))))))))
    (M.prod_mem pairing unions powers separation (M.prod_mem pairing unions powers separation hV hU) hB)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.externalSlotCopyEntryFormula 0 1 2 3 4 5 6 7 8 9) (extend z params))
      (ZFSet.prod (ZFSet.prod V U) B) = externalSlotCopyGraph V E I U B action images j := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_externalSlotCopyEntryFormula _ _ _ _ _ _ _ _ _ _ _ rfl]
    exact ⟨And.right, fun hz => ⟨(ZFSet.mem_sep.1 hz).1, hz⟩⟩
  exact equal ▸ selected
end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_RequestedOwnerSlotLaws
attribute [-instance] _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Family.child_countable _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Request.child_countable _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.TileRequests
open Attachment CosetGeometry
universe u
variable {A : Type u} {P : MeetOrder A}

namespace Request

theorem vertexSlot_lt_three (r : Request P) (i : Option r.Child) : r.vertexSlot i < 3 := by
  cases r with
  | separation W => cases i <;> simp [vertexSlot]
  | compression K copy => cases i <;> simp [vertexSlot]
  | rectangle rect =>
    cases i with
    | none => simp [vertexSlot]
    | some i => cases i with | up b => cases b <;> simp [vertexSlot]

end Request

end PartitionPilot.Compression.RecursiveMaps.TileRequests



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundExternalBirthLayers
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
universe u

namespace GroundExternalBirthData
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ P r μ A oldTimes oldBirth : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalBirthData M initial I Sources Reps G m one T τ P r μ A oldTimes oldBirth completion)

include data

theorem stamp_fiber (n : Nat) (x : ZFSet.{u}) :
    ZFSet.pair x (compressionStamp oldTimes n) ∈ data.birth ↔
      x ∈ ownerFresh (completion.externalSeedCarrier P r μ A) (completion.externalPointCarrier P r μ A) ∧
        ZFSet.pair x (natSetCode n) ∈ completion.externalOwnerLevels P r μ A := by
  apply ownerBirthGraph_stamp_fiber data.seed_function data.times.ownerStampCode
  · intro y a k t entry stamp
    rw [(data.times.entries k t).1 stamp]
    exact data.old_before entry k
  · exact (data.times.entries n _).2 rfl

end GroundExternalBirthData

end PartitionPilot.Forcing




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_ExternalRequestRankBounds
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

theorem externalRectangleBound_rank_lt {P G : ZFSet.{u}}
    (points : ZFSet.rank P < o) (actors : ZFSet.rank G < o) :
    ZFSet.rank (externalRectangleBound P G) < o :=
  rank_product_lt limit points (rank_product_lt limit points
    (rank_product_lt limit points (rank_product_lt limit actors actors)))

theorem externalRectangles_rank_lt {P G : ZFSet.{u}} (r μ A : ZFSet.{u})
    (points : ZFSet.rank P < o) (actors : ZFSet.rank G < o) :
    ZFSet.rank (externalRectangles P G r μ A) < o :=
  (ZFSet.rank_mono (show externalRectangles P G r μ A ⊆ externalRectangleBound P G from
    fun _ hx => (ZFSet.mem_sep.1 hx).1)).trans_lt
      (externalRectangleBound_rank_lt limit points actors)

theorem externalRequestCarrier_rank_lt {I P Rectangles : ZFSet.{u}}
    (indices : ZFSet.rank I < o) (points : ZFSet.rank P < o)
    (rectangles : ZFSet.rank Rectangles < o) :
    ZFSet.rank (externalRequestCarrier I P Rectangles) < o := by
  have tag := fun n => rank_singleton_lt limit (rank_natSetCode_lt limit n)
  rw [externalRequestCarrier, ZFSet.rank_union, ZFSet.rank_union]
  exact max_lt (max_lt (rank_product_lt limit (tag 0) indices)
    (rank_product_lt limit (tag 1) points)) (rank_product_lt limit (tag 2) rectangles)

theorem externalChildLetters_rank_lt {I P Rectangles : ZFSet.{u}}
    (indices : ZFSet.rank I < o) (points : ZFSet.rank P < o)
    (rectangles : ZFSet.rank Rectangles < o) :
    ZFSet.rank (externalChildLetters I P Rectangles) < o := by
  have tag := fun n => rank_singleton_lt limit (rank_natSetCode_lt limit n)
  rw [externalChildLetters, ZFSet.rank_union]
  exact max_lt
    (rank_product_lt limit (externalRequestCarrier_rank_lt limit indices points rectangles) (tag 0))
    (rank_product_lt limit (rank_product_lt limit (tag 2) rectangles) (tag 1))

theorem externalGeneratorAlphabet_rank_lt {G S : ZFSet.{u}}
    (actors : ZFSet.rank G < o) (letters : ZFSet.rank S < o) :
    ZFSet.rank (externalGeneratorAlphabet G S) < o := by
  rw [externalGeneratorAlphabet, ZFSet.rank_union]
  exact max_lt
    (rank_product_lt limit (rank_singleton_lt limit (rank_natSetCode_lt limit 0)) actors)
    (rank_product_lt limit (rank_singleton_lt limit (rank_natSetCode_lt limit 1))
      (rank_product_lt limit letters (rank_natSetCode_lt limit 2)))

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_ExternalStarCarrierRanks
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

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
include limit

theorem externalGroupCarrier_rank_lt {G S : ZFSet.{u}} (m one : ZFSet.{u})
    (omega : ZFSet.rank ZFSet.omega < o)
    (actors : ZFSet.rank G < o) (letters : ZFSet.rank S < o) :
    ZFSet.rank (M.externalGroupCarrier G S m one) < o :=
  rank_equivalenceClasses_lt limit (M.externalWordEquivalence G S m one)
    (M.finiteWords_rank_lt limit omega (externalGeneratorAlphabet_rank_lt limit actors letters))

theorem externalRequestGroup_rank_lt {I P G : ZFSet.{u}} (r μ A m one : ZFSet.{u})
    (omega : ZFSet.rank ZFSet.omega < o) (indices : ZFSet.rank I < o)
    (points : ZFSet.rank P < o) (actors : ZFSet.rank G < o) :
    ZFSet.rank (M.externalGroupCarrier G
      (externalChildLetters I P (externalRectangles P G r μ A)) m one) < o :=
  M.externalGroupCarrier_rank_lt limit m one omega actors
    (externalChildLetters_rank_lt limit indices points (externalRectangles_rank_lt limit r μ A points actors))

end TransitiveGround

namespace GroundCompressionCompletion
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)
variable {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
include limit

theorem externalPointCarrier_rank_lt {P r μ A : ZFSet.{u}}
    (actors : ZFSet.rank (M.externalGroupCarrier G
      (externalChildLetters I P (externalRectangles P G r μ A)) m one) < o)
    (completed : ZFSet.rank (completion.algebra.union.fields 0) < o) :
    ZFSet.rank (completion.externalPointCarrier P r μ A) < o :=
  rank_equivalenceClasses_lt limit (completion.externalFlatEquivalence P r μ A)
    (rank_product_lt limit actors completed)

theorem externalPointCarrier_rank_lt_of_inputs {P : ZFSet.{u}} (r μ A : ZFSet.{u})
    (omega : ZFSet.rank ZFSet.omega < o) (indices : ZFSet.rank I < o)
    (points : ZFSet.rank P < o) (actors : ZFSet.rank G < o)
    (completed : ZFSet.rank (completion.algebra.union.fields 0) < o) :
    ZFSet.rank (completion.externalPointCarrier P r μ A) < o :=
  completion.externalPointCarrier_rank_lt limit
    (M.externalRequestGroup_rank_lt limit r μ A m one omega indices points actors) completed

theorem externalBoundedCarrier_rank_lt {P : ZFSet.{u}} (r μ A : ZFSet.{u})
    (omega : ZFSet.rank ZFSet.omega < o) (indices : ZFSet.rank I < o)
    (points : ZFSet.rank P < o) (actors : ZFSet.rank G < o)
    (completed : ZFSet.rank (completion.algebra.union.fields 0) < o) :
    ZFSet.rank (completion.externalBoundedCarrier P r μ A) < o :=
  rank_fixedTopCarrier_lt limit
    (completion.externalPointCarrier_rank_lt_of_inputs limit r μ A omega indices points actors completed)

end GroundCompressionCompletion
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization
universe u
variable {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
include limit

theorem taggedSumCarrier_rank_lt {A B : ZFSet.{u}}
    (left : ZFSet.rank A < o) (right : ZFSet.rank B < o) :
    ZFSet.rank (taggedSumCarrier A B) < o := by
  rw [taggedSumCarrier, ZFSet.rank_union]
  exact max_lt
    (rank_product_lt limit (rank_singleton_lt limit (rank_natSetCode_lt limit 0)) left)
    (rank_product_lt limit (rank_singleton_lt limit (rank_natSetCode_lt limit 1)) right)

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem externalStarVertices_rank_lt {G S R : ZFSet.{u}} (m one : ZFSet.{u})
    (actors : ZFSet.rank (M.externalGroupCarrier G S m one) < o)
    (requests : ZFSet.rank R < o) :
    ZFSet.rank (M.externalStarVertices G S R m one) < o :=
  taggedSumCarrier_rank_lt limit
    (rank_equivalenceClasses_lt limit (M.externalCosetEquivalence G S m one) actors)
    (rank_product_lt limit actors requests)

theorem externalStarVertices_rank_lt_of_inputs {I P G : ZFSet.{u}}
    (r μ A m one : ZFSet.{u}) (omega : ZFSet.rank ZFSet.omega < o)
    (indices : ZFSet.rank I < o) (points : ZFSet.rank P < o)
    (actors : ZFSet.rank G < o) :
    ZFSet.rank (M.externalStarVertices G
      (externalChildLetters I P (externalRectangles P G r μ A))
      (externalRequestCarrier I P (externalRectangles P G r μ A)) m one) < o :=
  M.externalStarVertices_rank_lt limit m one
    (M.externalRequestGroup_rank_lt limit r μ A m one omega indices points actors)
    (externalRequestCarrier_rank_lt limit indices points
      (externalRectangles_rank_lt limit r μ A points actors))

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundLowRankFunctionGraphs
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

theorem functionGraphOn_rank_lt {I f : ZFSet.{u}} (hI : I ∈ K) (hf : f ∈ M.sets)
    (function : FunctionGraphOn I f)
    (values : ∀ i ∈ I, ∀ v, ZFSet.pair i v ∈ f → ZFSet.rank v < ZFSet.rank K) :
    ZFSet.rank f < ZFSet.rank K := by
  have hIM := M.transitive hK hI
  have smallI := GroundBelow.of_member pairing unions powers separation hK hI
  have smallF := smallI.functionGraphOn pairing unions powers separation hIM hf hK function
  have limit := conditions.rank_isLimit pairing unions powers separation infinite hK
  apply conditions.2.2.1.rank_lt_of_small pairing unions powers separation collection
    hf hK conditions.1 smallF
  intro z hz
  obtain ⟨i, hi, v, rfl⟩ := function.shape z hz
  exact rank_orderedPair_lt limit
    ((ZFSet.rank_lt_of_mem hi).trans (ZFSet.rank_lt_of_mem hI)) (values i hi v hz)

end PartitionPilot.Forcing.GroundInaccessibleConditions

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

namespace GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
variable {base old HQs Hrs Hμs t N z : ZFSet.{u}}
variable (births : GroundCompressionBirthData M state.data I Sources Reps G m one T data base old)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets)
variable {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
include pairing unions powers separation hI hSources hReps hG hT limit

theorem exists_birthWitness_to_finite_rank_lt (n k : Nat) (before : n ≤ k)
    (earlier : t ∈ compressionStamp base n) (hz : z ∈ M.sets) (rank : ZFSet.rank z < o)
    (code : GrowthLayerWitnessCode HQs Hrs Hμs
      (state.data.iterate M I Sources Reps G T n).D
      (state.data.iterate M I Sources Reps G T n).rD
      (state.data.iterate M I Sources Reps G T n).μD
      (graphRestriction (state.data.iterate M I Sources Reps G T n).D births.birth) t N z) :
    ∃ z' ∈ M.sets, GrowthLayerWitnessCode HQs Hrs Hμs
      (state.data.iterate M I Sources Reps G T k).D
      (state.data.iterate M I Sources Reps G T k).rD
      (state.data.iterate M I Sources Reps G T k).μD
      (graphRestriction (state.data.iterate M I Sources Reps G T k).D births.birth) t N z' ∧ ZFSet.rank z' < o := by
  have mono := fun n k h => (state.canonical_iterate_graphs_mono pairing unions powers separation
    hI hSources hReps hG hT (n := n) (k := k) h).1
  have growth := state.canonical_iterate_graphs_mono pairing unions powers separation
    hI hSources hReps hG hT before
  obtain ⟨current, equal⟩ := state.canonical_iterate_valid pairing unions powers separation
    hI hSources hReps hG hT n
  have ground : (state.data.iterate M I Sources Reps G T n).D ∈ M.sets := equal ▸ current.ground.carrier
  exact code.exists_literal_extension_rank_lt pairing unions separation ground hz limit rank growth.1 growth.2.1 growth.2.2.1
    (NatBirthExtensionCode.restriction_mono mono before)
    (fun _ _ entry => births.extension.earlier_fiber mono births.initial_function
      (fun _ _ h => compressionStamp_subset base h) n earlier
      (pair_mem_graphRestriction.1 entry).1)

theorem exists_birthWitness_to_union_rank_lt (n : Nat) (before : t ∈ compressionStamp base n)
    (hz : z ∈ M.sets) (rank : ZFSet.rank z < o)
    (code : GrowthLayerWitnessCode HQs Hrs Hμs
      (state.data.iterate M I Sources Reps G T n).D
      (state.data.iterate M I Sources Reps G T n).rD
      (state.data.iterate M I Sources Reps G T n).μD
      (graphRestriction (state.data.iterate M I Sources Reps G T n).D births.birth) t N z) :
    ∃ z' ∈ M.sets, GrowthLayerWitnessCode HQs Hrs Hμs
      (data.fields 0) (data.fields 1) (data.fields 2) births.birth t N z' ∧ ZFSet.rank z' < o := by
  have mono := fun n k h => (state.canonical_iterate_graphs_mono pairing unions powers separation
    hI hSources hReps hG hT (n := n) (k := k) h).1
  obtain ⟨current, equal⟩ := state.canonical_iterate_valid pairing unions powers separation
    hI hSources hReps hG hT n
  have ground : (state.data.iterate M I Sources Reps G T n).D ∈ M.sets := equal ▸ current.ground.carrier
  exact code.exists_literal_extension_rank_lt pairing unions separation ground hz limit rank
    ((data.fieldUnion 0).subset n) ((data.fieldUnion 1).subset n) ((data.fieldUnion 2).subset n)
    (graphRestriction_subset (state.data.iterate M I Sources Reps G T n).D births.birth)
    (fun _ _ entry => births.extension.earlier_fiber mono births.initial_function
      (fun _ _ h => compressionStamp_subset base h) n before entry)

theorem exists_priorWitness_to_finite_rank_lt (k : Nat) (before : t ∈ base ∨ t = base) (hz : z ∈ M.sets) (rank : ZFSet.rank z < o)
    (code : GrowthLayerWitnessCode HQs Hrs Hμs state.data.D state.data.rD state.data.μD old t N z) :
    ∃ z' ∈ M.sets, GrowthLayerWitnessCode HQs Hrs Hμs
      (state.data.iterate M I Sources Reps G T k).D
      (state.data.iterate M I Sources Reps G T k).rD
      (state.data.iterate M I Sources Reps G T k).μD
      (graphRestriction (state.data.iterate M I Sources Reps G T k).D births.birth) t N z' ∧ ZFSet.rank z' < o := by
  apply state.exists_birthWitness_to_finite_rank_lt data births pairing unions powers separation hI hSources hReps hG hT limit
    0 k (Nat.zero_le k) (compressionStamp_old_mem before 0) hz rank
  simpa only [RecursiveStateData.iterate_zero, births.original] using code

theorem exists_priorWitness_to_union_rank_lt (before : t ∈ base ∨ t = base) (hz : z ∈ M.sets) (rank : ZFSet.rank z < o)
    (code : GrowthLayerWitnessCode HQs Hrs Hμs state.data.D state.data.rD state.data.μD old t N z) :
    ∃ z' ∈ M.sets, GrowthLayerWitnessCode HQs Hrs Hμs
      (data.fields 0) (data.fields 1) (data.fields 2) births.birth t N z' ∧ ZFSet.rank z' < o := by
  apply state.exists_birthWitness_to_union_rank_lt data births pairing unions powers separation hI hSources hReps hG hT limit
    0 (compressionStamp_old_mem before 0) hz rank
  simpa only [RecursiveStateData.iterate_zero, births.original] using code

omit unions powers separation hI hSources hReps hG hT in
theorem exists_limitWitness_rank_lt :
    ∃ z ∈ M.sets, GrowthLayerWitnessCode HQs Hrs Hμs
      (data.fields 0) (data.fields 1) (data.fields 2) births.birth births.limit N z ∧ ZFSet.rank z < o := by
  have hEmpty := M.empty_mem ⟨data.fields 0, data.ground 0⟩
  exact ⟨countableLayerWitness ∅ ∅, M.countableLayerWitness_mem pairing hEmpty hEmpty,
    Or.inl ⟨∅, ∅, rfl, ⟨InjectionCode.empty N, fun x _ entry => (births.no_limit_birth x entry).elim⟩⟩,
    countableLayerWitness_rank_lt limit (by simpa only [ZFSet.rank_empty] using limit.pos)
      (by simpa only [ZFSet.rank_empty] using limit.pos)⟩

end GroundCompressionState

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundTaggedComponentGraphs
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

theorem pair_mem_taggedComponentGraph (P I B N x i : ZFSet.{u}) :
    ZFSet.pair x i ∈ taggedComponentGraph P I B N ↔
      i ∈ I ∧ ∃ q ∈ B, ZFSet.pair i q ∈ N ∧ x = ZFSet.pair P (ZFSet.pair i q) := by
  rw [taggedComponentGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, y, _, j, hj, n, hn, q, hq, equal, value, rfl⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hj, q, hq, hn, value⟩
  · rintro ⟨hi, q, hq, hn, rfl⟩
    have hx : ZFSet.pair P (ZFSet.pair i q) ∈ ZFSet.prod {P} N := ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_singleton.2 rfl, hn⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hx, hi⟩, _, hx, i, hi, _, hn, q, hq, rfl, rfl, rfl⟩

theorem taggedComponentGraph_function {P I B N : ZFSet.{u}} (subset : N ⊆ ZFSet.prod I B) :
    ZFSet.IsFunc (ZFSet.prod {P} N) I (taggedComponentGraph P I B N) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro x hx
  obtain ⟨p, hp, n, hn, rfl⟩ := ZFSet.mem_prod.1 hx
  obtain rfl := ZFSet.mem_singleton.1 hp
  obtain ⟨i, hi, q, hq, rfl⟩ := ZFSet.mem_prod.1 (subset hn)
  refine ⟨i, (pair_mem_taggedComponentGraph _ _ _ _ _ _).2 ⟨hi, q, hq, hn, rfl⟩, ?_⟩
  intro j hj
  obtain ⟨_, r, _, _, equal⟩ := (pair_mem_taggedComponentGraph _ _ _ _ _ _).1 hj
  exact ((ZFSet.pair_inj.1 ((ZFSet.pair_inj.1 equal).2)).1).symm

namespace BoundedFormula

theorem truth_taggedComponentFormula (env : Fin 6 → ZFSet.{u}) :
    Truth taggedComponentFormula env ↔
      ∃ x ∈ env 1, ∃ i ∈ env 2, ∃ n ∈ env 3, ∃ q ∈ env 4,
        env 0 = ZFSet.pair x i ∧ x = ZFSet.pair (env 5) n ∧ n = ZFSet.pair i q := by
  simp only [taggedComponentFormula, truth_exMem, Truth, truth_orderedPairFormula]
  rfl
end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem taggedComponentGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P I B N : ZFSet.{u}} (hP : P ∈ M.sets) (hI : I ∈ M.sets)
    (hB : B ∈ M.sets) (hN : N ∈ M.sets) : taggedComponentGraph P I B N ∈ M.sets := by
  have hSingle : ({P} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hP hP
  have hF := M.prod_mem pairing unions powers separation hSingle hN
  let params := extend (ZFSet.prod {P} N) (extend I (extend N (extend B (extend P Fin.elim0))))
  have selected := M.bounded_separation_mem separation BoundedFormula.taggedComponentFormula params
    (Fin.cases hF (Fin.cases hI (Fin.cases hN (Fin.cases hB (Fin.cases hP (fun j => Fin.elim0 j))))))
    (M.prod_mem pairing unions powers separation hF hI)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth BoundedFormula.taggedComponentFormula
      (extend z params)) (ZFSet.prod (ZFSet.prod {P} N) I) = taggedComponentGraph P I B N := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, taggedComponentGraph, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_taggedComponentFormula _)
  exact equal ▸ selected
end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundConstantBatchLayers
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem batchTemplateGraph_eq_section_dup1 (I P Qs rs As Es i : ZFSet.{u}) :
    batchTemplateGraph I P Qs rs As Es i =
      indexedRelationSection (familyPointBound Qs)
        (taggedExtension P (indexedAttachmentFresh I Qs rs As))
        (batchAttachmentTemplateGraph I P Qs rs As Es) i := by
  apply ZFSet.ext
  intro z
  rw [batchTemplateGraph, ZFSet.mem_sep, mem_indexedRelationSection]
  constructor
  · exact fun h => h.2
  · rintro ⟨q, hq, y, hy, rfl, entry⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hq, hy⟩, q, hq, y, hy, rfl, entry⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem batchTemplateFamily_spec
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I P Qs rs As Es : ZFSet.{u}} (hI : I ∈ M.sets) (hP : P ∈ M.sets)
    (hQs : Qs ∈ M.sets) (hrs : rs ∈ M.sets) (hAs : As ∈ M.sets) (hEs : Es ∈ M.sets) :
    M.batchTemplateFamilyBound I P Qs rs As ∈ M.sets ∧
      M.batchTemplateFamily I P Qs rs As Es ∈ M.sets ∧
      ZFSet.IsFunc I (M.batchTemplateFamilyBound I P Qs rs As)
        (M.batchTemplateFamily I P Qs rs As Es) ∧
      ∀ i e, ZFSet.pair i e ∈ M.batchTemplateFamily I P Qs rs As Es ↔
        i ∈ I ∧ e = batchTemplateGraph I P Qs rs As Es i := by
  have hPoints := M.familyPointBound_mem unions hQs
  have hL := M.taggedExtension_mem pairing unions powers separation hP
    (M.indexedAttachmentFresh_mem pairing unions powers separation hI hQs hrs hAs)
  have hGraph := M.batchAttachmentTemplateGraph_mem pairing unions powers separation hI hP hQs hrs hAs hEs
  have spec := M.indexedRelationSections_spec pairing unions powers separation hI hPoints hL hGraph
  refine ⟨M.groundRelations_mem pairing unions powers separation hPoints hL, spec.1, spec.2.1, ?_⟩
  intro i e
  exact (spec.2.2 i e).trans (and_congr Iff.rfl (by rw [batchTemplateGraph_eq_section_dup1]))

end TransitiveGround

namespace AttachmentBatchInputs
variable {M : TransitiveGround.{u}}
variable {P r μ I Qs rs μs As Es Fs Ss : ZFSet.{u}}
variable (d : AttachmentBatchInputs P r μ I Qs rs μs As Es Fs Ss)

theorem batchIncomingFiber_eq {birth stamp : ZFSet.{u}}
    (earlier : ∀ x t, ZFSet.pair x t ∈ birth → t ∈ stamp) :
    d.batchIncomingFiber = layerBirthFiber d.batchCarrier (d.batchBirth birth stamp) stamp := by
  apply ZFSet.ext
  intro x
  rw [mem_layerBirthFiber]
  constructor
  · intro hx
    exact ⟨ZFSet.mem_union.2 (Or.inr hx), (taggedBirth_stamp_iff earlier).2 hx⟩
  · exact fun hx => (taggedBirth_stamp_iff earlier).1 hx.2

theorem batchIncomingComponents_function :
    ZFSet.IsFunc d.batchIncomingFiber I d.batchIncomingComponents :=
  taggedComponentGraph_function (fun _ hn => indexedAttachmentDomain_subset I Qs
    (indexedAttachmentFresh_subset I Qs rs As hn))

theorem batchIncomingComponents_encode (q : d.templates.Fresh) {i : ZFSet.{u}}
    (entry : ZFSet.pair (d.coding.encode (.inr q)) i ∈ d.batchIncomingComponents) :
    q.1.val = i := by
  obtain ⟨_, z, _, _, equal⟩ := (pair_mem_taggedComponentGraph _ _ _ _ _ _).1 entry
  change ZFSet.pair P (ZFSet.pair q.1.val q.2.val.val) = ZFSet.pair P (ZFSet.pair i z) at equal
  exact (ZFSet.pair_inj.1 (ZFSet.pair_inj.1 equal).2).1

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hP : P ∈ M.sets) (hI : I ∈ M.sets) (hQs : Qs ∈ M.sets)
variable (hrs : rs ∈ M.sets) (hAs : As ∈ M.sets) (hEs : Es ∈ M.sets)

include pairing unions powers separation hP hI hQs hrs hAs in
theorem batchIncomingComponents_ground :
    d.batchIncomingFiber ∈ M.sets ∧ d.batchIncomingComponents ∈ M.sets := by
  have hN := M.indexedAttachmentFresh_mem pairing unions powers separation hI hQs hrs hAs
  have hSingle : ({P} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hP hP
  exact ⟨M.prod_mem pairing unions powers separation hSingle hN,
    M.taggedComponentGraph_mem pairing unions powers separation hP hI
      (M.familyPointBound_mem unions hQs) hN⟩

include pairing unions powers separation hP hI hQs hrs hAs hEs in
theorem batchSeparatedLayerCode
    {HQs Hrs Hμs HTime T birth stamp Indices : ZFSet.{u}}
    (historySpaces : FunctionGraphOn HTime HQs)
    (historyOrders : FunctionGraphOn HTime Hrs)
    (historyMeets : FunctionGraphOn HTime Hμs)
    (born : ZFSet.IsFunc P T birth)
    (earlier : ∀ x t, ZFSet.pair x t ∈ birth → t ∈ stamp)
    (indices : ZFSet.IsFunc I stamp Indices)
    (sourceMatches : ∀ i : {i : ZFSet.{u} // i ∈ I}, ∀ s,
      ZFSet.pair i.val s ∈ Indices →
        ZFSet.pair s (d.space i) ∈ HQs ∧ ZFSet.pair s (d.rel i) ∈ Hrs ∧
        ZFSet.pair s (d.meet i) ∈ Hμs) :
    SeparatedLayerCode HQs Hrs Hμs d.batchCarrier d.batchOrder d.batchMeetGraph
      (d.batchBirth birth stamp) stamp I Indices (M.batchTemplateFamily I P Qs rs As Es)
      (M.batchTemplateFamilyBound I P Qs rs As) d.batchIncomingComponents d.batchIncomingFiber := by
  have maps := M.batchTemplateFamily_spec pairing unions powers separation hI hP hQs hrs hAs hEs
  refine ⟨indices, maps.2.2.1, d.batchIncomingFiber_eq earlier,
    d.batchIncomingComponents_function, ?_, ?_, ?_⟩
  · intro i hi s _ e Q R V indexEntry mapEntry spaceEntry orderEntry meetEntry
    let j : {i : ZFSet.{u} // i ∈ I} := ⟨i, hi⟩
    have matching :=  sourceMatches j s indexEntry
    have qeq := historySpaces.unique spaceEntry matching.1
    have req := historyOrders.unique orderEntry matching.2.1
    have veq := historyMeets.unique meetEntry matching.2.2
    have eeq := ((maps.2.2.2 i e).1 mapEntry).2
    subst Q R V e
    exact d.batch_template_embedding_code j
  · intro i hi s _ e Q x hx indexEntry mapEntry spaceEntry componentEntry
    let j : {i : ZFSet.{u} // i ∈ I} := ⟨i, hi⟩
    have qeq := historySpaces.unique spaceEntry (sourceMatches j s indexEntry).1
    have eeq := ((maps.2.2.2 i e).1 mapEntry).2
    subst Q e
    obtain ⟨_, q, _, fresh, rfl⟩ := (pair_mem_taggedComponentGraph _ _ _ _ _ _).1 componentEntry
    have qFresh := (pair_mem_indexedAttachmentFresh_of_entries d.spaces d.relations d.anchors
      (d.space_entry j) (d.rel_entry j) (d.anchor_entry j)).1 fresh
    exact (mem_relationImage _ _ _ _).2 ⟨hx, q, (mem_freshPart _ _ _ _).1 qFresh |>.1,
      (pair_mem_batchTemplateGraph _ _ _ _ _ _ _ _ _).2
        ((d.batch_template_entry_iff j q _).2 (Or.inr ⟨qFresh, rfl⟩))⟩
  · intro x hx y hy i _ j _ componentX componentY different
    obtain ⟨qx, eqx⟩ := d.batchBirth_fresh_cases earlier ((taggedBirth_stamp_iff earlier).2 hx)
    obtain ⟨qy, eqy⟩ := d.batchBirth_fresh_cases earlier ((taggedBirth_stamp_iff earlier).2 hy)
    have first := d.batchIncomingComponents_encode qx (eqx.symm ▸ componentX)
    have second := d.batchIncomingComponents_encode qy (eqy.symm ▸ componentY)
    have neq : qx.1 ≠ qy.1 := fun equal => different
      (first.symm.trans ((congrArg Subtype.val equal).trans second))
    exact eqx ▸ eqy ▸ d.batchBirth_different_components_bridge born earlier qx qy neq

include pairing unions powers separation hP hI hQs hrs hAs hEs in
theorem batchSeparatedWitness
    {HQs Hrs Hμs HTime T birth stamp Indices N : ZFSet.{u}}
    (historySpaces : FunctionGraphOn HTime HQs)
    (historyOrders : FunctionGraphOn HTime Hrs)
    (historyMeets : FunctionGraphOn HTime Hμs)
    (born : ZFSet.IsFunc P T birth)
    (earlier : ∀ x t, ZFSet.pair x t ∈ birth → t ∈ stamp)
    (hIndices : Indices ∈ M.sets) (indices : ZFSet.IsFunc I stamp Indices)
    (sourceMatches : ∀ i : {i : ZFSet.{u} // i ∈ I}, ∀ s,
      ZFSet.pair i.val s ∈ Indices →
        ZFSet.pair s (d.space i) ∈ HQs ∧ ZFSet.pair s (d.rel i) ∈ Hrs ∧
        ZFSet.pair s (d.meet i) ∈ Hμs) :
    let z := separatedLayerWitness I Indices (M.batchTemplateFamily I P Qs rs As Es)
      (M.batchTemplateFamilyBound I P Qs rs As) d.batchIncomingComponents d.batchIncomingFiber
    z ∈ M.sets ∧ GrowthLayerWitnessCode HQs Hrs Hμs d.batchCarrier d.batchOrder d.batchMeetGraph
      (d.batchBirth birth stamp) stamp N z := by
  have maps := M.batchTemplateFamily_spec pairing unions powers separation hI hP hQs hrs hAs hEs
  have components := d.batchIncomingComponents_ground pairing unions powers separation hP hI hQs hrs hAs
  exact ⟨M.separatedLayerWitness_mem pairing unions hI hIndices maps.2.1 maps.1 components.2 components.1,
    Or.inr (Or.inr ⟨I, Indices, _, _, _, _, rfl,
      d.batchSeparatedLayerCode pairing unions powers separation hP hI hQs hrs hAs hEs
        historySpaces historyOrders historyMeets born earlier indices sourceMatches⟩)⟩

end AttachmentBatchInputs

namespace AttachmentBatchInputs
variable {M : TransitiveGround.{u}}
variable {P r μ I Qs rs μs As Es Fs Ss : ZFSet.{u}}
variable (d : AttachmentBatchInputs P r μ I Qs rs μs As Es Fs Ss)

theorem constantBatchLayerWitness_spec
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hP : P ∈ M.sets) (hI : I ∈ M.sets) (hQs : Qs ∈ M.sets)
    (hrs : rs ∈ M.sets) (hAs : As ∈ M.sets) (hEs : Es ∈ M.sets)
    {HQs Hrs Hμs HTime T birth stamp τ P0 r0 μ0 N : ZFSet.{u}}
    (historySpaces : FunctionGraphOn HTime HQs)
    (historyOrders : FunctionGraphOn HTime Hrs)
    (historyMeets : FunctionGraphOn HTime Hμs)
    (born : ZFSet.IsFunc P T birth)
    (earlier : ∀ x t, ZFSet.pair x t ∈ birth → t ∈ stamp)
    (hStamp : stamp ∈ M.sets) (before : τ ∈ stamp)
    (constant : ∀ i, d.space i = P0 ∧ d.rel i = r0 ∧ d.meet i = μ0)
    (source : ZFSet.pair τ P0 ∈ HQs ∧ ZFSet.pair τ r0 ∈ Hrs ∧ ZFSet.pair τ μ0 ∈ Hμs) :
    d.constantBatchLayerWitness M τ ∈ M.sets ∧
      GrowthLayerWitnessCode HQs Hrs Hμs d.batchCarrier d.batchOrder d.batchMeetGraph
        (d.batchBirth birth stamp) stamp N (d.constantBatchLayerWitness M τ) := by
  have indices : ZFSet.IsFunc I stamp (constantFamilyGraph I τ) := by
    refine ⟨?_, (constantFamilyGraph_function I τ).2⟩
    intro z hz
    obtain ⟨i, hi, s, hs, rfl⟩ := ZFSet.mem_prod.1 ((constantFamilyGraph_function I τ).1 hz)
    obtain rfl := ZFSet.mem_singleton.1 hs
    exact ZFSet.pair_mem_prod.2 ⟨hi, before⟩
  apply d.batchSeparatedWitness pairing unions powers separation hP hI hQs hrs hAs hEs
    historySpaces historyOrders historyMeets born earlier
    (M.constantFamilyGraph_mem pairing unions powers separation hI (M.transitive hStamp before)) indices
  intro i s entry
  obtain rfl := ((pair_mem_constantFamilyGraph I τ i.val s).1 entry).2
  simpa only [(constant i).1, (constant i).2.1, (constant i).2.2] using source

end AttachmentBatchInputs
end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundCompressionIncomingWitnessRanks
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
open SetRealization
universe u

theorem batchFamilyPointBound_rank_le (Qs : ZFSet.{u}) :
    ZFSet.rank (familyPointBound Qs) ≤ ZFSet.rank Qs :=
  (ZFSet.rank_sUnion_le _).trans ((ZFSet.rank_sUnion_le _).trans (ZFSet.rank_sUnion_le _))

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
include limit

theorem batchTemplateFamilyBound_rank_lt {I P Qs : ZFSet.{u}} (rs As : ZFSet.{u})
    (points : ZFSet.rank P < o) (indices : ZFSet.rank I < o)
    (spaces : ZFSet.rank Qs < o) :
    ZFSet.rank (M.batchTemplateFamilyBound I P Qs rs As) < o := by
  have source := (batchFamilyPointBound_rank_le Qs).trans_lt spaces
  have fresh := (ZFSet.rank_mono (fun z hz => indexedAttachmentDomain_subset I Qs
    (indexedAttachmentFresh_subset I Qs rs As hz))).trans_lt (rank_product_lt limit indices source)
  exact M.groundRelations_rank_lt limit source (rank_taggedExtension_lt limit points fresh)

theorem batchTemplateFamily_rank_lt {I P Qs : ZFSet.{u}} (rs As Es : ZFSet.{u})
    (points : ZFSet.rank P < o) (indices : ZFSet.rank I < o)
    (spaces : ZFSet.rank Qs < o) :
    ZFSet.rank (M.batchTemplateFamily I P Qs rs As Es) < o := by
  have subset : M.batchTemplateFamily I P Qs rs As Es ⊆
      ZFSet.prod I (M.batchTemplateFamilyBound I P Qs rs As) := by
    intro z hz
    unfold batchTemplateFamily indexedRelationSections at hz
    exact (ZFSet.mem_sep.1 hz).1
  exact (ZFSet.rank_mono subset).trans_lt (rank_product_lt limit indices
    (M.batchTemplateFamilyBound_rank_lt limit rs As points indices spaces))

end TransitiveGround

namespace AttachmentBatchInputs
variable {M : TransitiveGround.{u}}
variable {P r μ I Qs rs μs As Es Fs Ss : ZFSet.{u}}
variable (d : AttachmentBatchInputs P r μ I Qs rs μs As Es Fs Ss)
variable {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
include limit

theorem batchIncomingFiber_rank_lt
    (points : ZFSet.rank P < o) (indices : ZFSet.rank I < o)
    (spaces : ZFSet.rank Qs < o) : ZFSet.rank d.batchIncomingFiber < o := by
  have fresh := (ZFSet.rank_mono (fun z hz => indexedAttachmentDomain_subset I Qs
    (indexedAttachmentFresh_subset I Qs rs As hz))).trans_lt
      (rank_product_lt limit indices ((batchFamilyPointBound_rank_le Qs).trans_lt spaces))
  exact rank_product_lt limit (rank_singleton_lt limit points) fresh

theorem constantBatchLayerWitness_rank_lt (M : TransitiveGround.{u}) {τ : ZFSet.{u}}
    (points : ZFSet.rank P < o) (indices : ZFSet.rank I < o)
    (spaces : ZFSet.rank Qs < o) (time : ZFSet.rank τ < o) :
    ZFSet.rank (d.constantBatchLayerWitness M τ) < o := by
  have fiber := d.batchIncomingFiber_rank_lt limit points indices spaces
  exact separatedLayerWitness_rank_lt limit indices
    (rank_constantFamilyGraph_lt limit indices time)
    (M.batchTemplateFamily_rank_lt limit rs As Es points indices spaces)
    (M.batchTemplateFamilyBound_rank_lt limit rs As points indices spaces)
    (rank_functionGraph_lt limit d.batchIncomingComponents_function fiber indices) fiber

end AttachmentBatchInputs

end

namespace GroundCompressionState
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
variable {base old : ZFSet.{u}}
variable (births : GroundCompressionBirthData M state.data I Sources Reps G m one T data base old)

theorem exists_canonicalIncomingRankedWitness
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets)
    (constant : RecursiveTemplateConstancy P0 r0 μ0 state.data)
    {HQs Hrs Hμs HTime N : ZFSet.{u}}
    (historySpaces : FunctionGraphOn HTime HQs)
    (historyOrders : FunctionGraphOn HTime Hrs)
    (historyMeets : FunctionGraphOn HTime Hμs)
    (source : ZFSet.pair base P0 ∈ HQs ∧ ZFSet.pair base r0 ∈ Hrs ∧ ZFSet.pair base μ0 ∈ Hμs)
    {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (points : ZFSet.rank state.data.D < o) (indices : ZFSet.rank state.data.J < o)
    (templates : ZFSet.rank P0 < o) (tasks : ZFSet.rank I < o)
    (time : ZFSet.rank base < o) (n : Nat) :
    ∃ z ∈ M.sets, ZFSet.rank z < o ∧ GrowthLayerWitnessCode HQs Hrs Hμs
      (state.data.iterate M I Sources Reps G T (n + 1)).D
      (state.data.iterate M I Sources Reps G T (n + 1)).rD
      (state.data.iterate M I Sources Reps G T (n + 1)).μD
      (graphRestriction (state.data.iterate M I Sources Reps G T (n + 1)).D births.birth)
      (compressionStamp base n) N z := by
  let current := state.iterate pairing unions powers separation hI hSources hReps hG hT n
  have equal : current.data = state.data.iterate M I Sources Reps G T n :=
    state.iterate_data pairing unions powers separation hI hSources hReps hG hT n
  have currentConstant : RecursiveTemplateConstancy P0 r0 μ0 current.data := by
    simpa only [equal] using constant.iterate M I Sources Reps G T n
  have finite : ZFSet.IsFunc current.data.D births.limit
      (graphRestriction (state.data.iterate M I Sources Reps G T n).D births.birth) := by
    simpa only [equal] using state.canonical_birth_function data pairing unions powers separation
      hI hSources hReps hG hT births.extension births.initial_function births.times n
  have earlier : ∀ x t, ZFSet.pair x t ∈
      graphRestriction (state.data.iterate M I Sources Reps G T n).D births.birth →
      t ∈ compressionStamp base n := fun _ _ entry =>
    state.canonical_birth_before_stamp pairing unions powers separation hI hSources hReps hG hT
      births.extension births.initial_bound n entry
  have result := current.batch.constantBatchLayerWitness_spec pairing unions powers separation
    current.ground.carrier current.ground.indices current.ground.spaces current.ground.relations
    current.ground.anchors current.ground.embeddings historySpaces historyOrders historyMeets finite earlier
    (M.transitive births.limit_ground (births.times.stamp_mem_limit n)) (compressionStamp_base_mem base n)
    (fun i => ⟨((currentConstant.space_entry_iff _ _).1 (current.batch.space_entry i)).2,
      ((currentConstant.relation_entry_iff _ _).1 (current.batch.rel_entry i)).2,
      ((currentConstant.meet_entry_iff _ _).1 (current.batch.meet_entry i)).2⟩) source (N := N)
  have finiteRanks := constant.iterate_carrier_ranks M I Sources Reps G T limit
    points indices templates tasks n
  have pointRank : ZFSet.rank current.data.D < o := by simpa only [equal] using finiteRanks.1
  have indexRank : ZFSet.rank current.data.J < o := by simpa only [equal] using finiteRanks.2
  have spaceRank : ZFSet.rank current.data.Qs < o := by
    rw [currentConstant.spaces]
    exact rank_constantFamilyGraph_lt limit indexRank templates
  have witnessRank := current.batch.constantBatchLayerWitness_rank_lt limit M
    pointRank indexRank spaceRank time
  refine ⟨current.batch.constantBatchLayerWitness M base, result.1, witnessRank, ?_⟩
  have code := result.2
  change GrowthLayerWitnessCode HQs Hrs Hμs current.data.currentCarrier
    current.data.currentOrder current.data.currentMeet
    (taggedBirth current.data.D current.data.fresh
      (graphRestriction (state.data.iterate M I Sources Reps G T n).D births.birth)
      (compressionStamp base n)) (compressionStamp base n) N _ at code
  rw [state.canonical_birth_step pairing unions powers separation hI hSources hReps hG hT
    births.extension births.initial_function n]
  simpa only [equal, RecursiveStateData.iterate_succ, RecursiveStateData.successor] using code

end GroundCompressionState

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundExternalRawPriorLayers
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroundExternalBirthData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 oldTimes oldBirth C D rD lo hi seed T0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 oldTimes oldBirth completion)
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (action : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)

local notation "U" => completion.algebra.union.fields 0
local notation "B" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "E" => completion.externalIdentityCopyGraph P0 r0 μ0 A0

include births in
theorem priorFiber_image {t y : ZFSet.{u}}
    (oldTime : t ∈ oldTimes ∨ t = oldTimes) (born : ZFSet.pair y t ∈ births.birth) :
    ∃ x ∈ U, ZFSet.pair x y ∈ E := by
  rcases (pair_mem_ownerBirthGraph _ _ _ _ _ _ _ _).1 born with oldEntry | freshEntry
  · exact (mem_relationImage U B E y).1
      (ZFSet.pair_mem_prod.1 (births.seed_function.1 oldEntry)).1 |>.2
  · obtain ⟨_, _, _, n, hn, _, stamp⟩ := freshEntry
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
    have later := compressionStamp_old_mem oldTime n
    rw [← (births.times.entries n t).1 stamp] at later
    exact (ZFSet.mem_irrefl t later).elim

end PartitionPilot.Forcing.GroundExternalBirthData

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundCompressionCarrierRankBounds
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

namespace GroundInaccessibleConditions
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}

theorem exists_rank_limit_above (conditions : GroundInaccessibleConditions M K)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (hK : K ∈ M.sets) {o : Ordinal.{u}} (bound : o < ZFSet.rank K) :
    ∃ L ∈ K, Order.IsSuccLimit (ZFSet.rank L) ∧ o < ZFSet.rank L := by
  have hBase : ordinalCode o ∈ K := by
    rw [ordinalSetProperty_eq_code_rank K conditions.1]
    exact (mem_ordinalCode_iff o (ZFSet.rank K)).2 bound
  obtain ⟨_, _, L, _, _, _, hL, limit, above⟩ := M.exists_groundCompressionStamps_below
    pairing unions powers separation collection infinite hK conditions hBase
  refine ⟨L, hL, limit, ?_⟩
  simpa only [rank_ordinalCode] using ZFSet.rank_lt_of_mem above

end GroundInaccessibleConditions

namespace GroundCompressionUnionData
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T : ZFSet.{u}}
variable (data : GroundCompressionUnionData M initial I Sources Reps G m one T)

theorem carrier_rank_lt_inaccessible
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    {K P r μ : ZFSet.{u}} (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    (constant : RecursiveTemplateConstancy P r μ initial)
    (points : ZFSet.rank initial.D < ZFSet.rank K) (indices : ZFSet.rank initial.J < ZFSet.rank K)
    (templates : ZFSet.rank P < ZFSet.rank K) (tasks : ZFSet.rank I < ZFSet.rank K) :
    ZFSet.rank (data.fields 0) < ZFSet.rank K := by
  let b := max (ZFSet.rank initial.D) (max (ZFSet.rank initial.J) (max (ZFSet.rank P) (ZFSet.rank I)))
  have bound : b < ZFSet.rank K := max_lt points (max_lt indices (max_lt templates tasks))
  obtain ⟨L, hL, limit, above⟩ := conditions.exists_rank_limit_above
    pairing unions powers separation collection infinite hK bound
  have pointBound : ZFSet.rank initial.D ≤ b := le_max_left _ _
  have indexBound : ZFSet.rank initial.J ≤ b := (le_max_left _ _).trans (le_max_right _ _)
  have templateBound : ZFSet.rank P ≤ b :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have taskBound : ZFSet.rank I ≤ b :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  exact (data.carrier_rank_le constant limit (pointBound.trans_lt above) (indexBound.trans_lt above)
    (templateBound.trans_lt above) (taskBound.trans_lt above)).trans_lt (ZFSet.rank_lt_of_mem hL)

end GroundCompressionUnionData

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem initialCompressionUnion_rank_lt
    {P G r μ A Labels Sources Reps m one T K : ZFSet.{u}}
    (data : GroundCompressionUnionData M (M.initialCompressionData P G r μ A Labels)
      (M.groundEligibleTasks P G r μ A Labels) Sources Reps G m one T)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    (points : ZFSet.rank P < ZFSet.rank K) (labels : ZFSet.rank Labels < ZFSet.rank K) :
    ZFSet.rank (data.fields 0) < ZFSet.rank K := by
  have limit := conditions.rank_isLimit pairing unions powers separation infinite hK
  have tasks := M.groundEligibleTasks_rank_lt limit G r μ A points labels
  exact data.carrier_rank_lt_inaccessible pairing unions powers separation collection infinite hK conditions
    (M.initialCompressionData_template_constancy P G r μ A Labels) points tasks points tasks

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainSuccessorProfilePreservation
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace GroundInitialMainSuccessorData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD Labels : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)
local notation "completion" => certificate.compression.born.profiled.heighted.completion

theorem target_rank_lt_of_components {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (omega : ZFSet.rank ZFSet.omega < o)
    (indices : ZFSet.rank (source.stage.compressionTasks Labels) < o)
    (points : ZFSet.rank source.stage.carrier < o)
    (actors : ZFSet.rank source.stage.actors < o)
    (completed : ZFSet.rank ((completion).algebra.union.fields 0) < o) :
    ZFSet.rank certificate.target.stage.carrier < o ∧
      ZFSet.rank certificate.target.stage.actors < o := by
  constructor
  · rw [certificate.target_fields.1]
    exact (completion).externalBoundedCarrier_rank_lt limit source.stage.order source.stage.meetGraph
      source.stage.action omega indices points actors completed
  · rw [certificate.target_fields.2.2.2.1]
    exact M.externalRequestGroup_rank_lt limit source.stage.order source.stage.meetGraph
      source.stage.action source.stage.multiplication source.stage.identity omega indices points actors

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
variable {K : ZFSet.{u}} (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
variable (points : ZFSet.rank source.stage.carrier < ZFSet.rank K)
variable (labels : ZFSet.rank Labels < ZFSet.rank K)
include certificate pairing unions powers separation collection infinite hK conditions points labels

theorem compression_union_rank_lt :
    ZFSet.rank ((completion).algebra.union.fields 0) < ZFSet.rank K :=
  M.initialCompressionUnion_rank_lt (completion).algebra.union
    pairing unions powers separation collection infinite hK conditions points labels

theorem target_rank_lt (actors : ZFSet.rank source.stage.actors < ZFSet.rank K) :
    ZFSet.rank certificate.target.stage.carrier < ZFSet.rank K ∧
      ZFSet.rank certificate.target.stage.actors < ZFSet.rank K := by
  have limit := conditions.rank_isLimit pairing unions powers separation infinite hK
  have tasks := M.groundEligibleTasks_rank_lt limit source.stage.actors source.stage.order
    source.stage.meetGraph source.stage.action points labels
  exact certificate.target_rank_lt_of_components limit (ZFSet.rank_lt_of_mem conditions.2.1)
    tasks points actors
    (certificate.compression_union_rank_lt pairing unions powers separation collection infinite
      hK conditions points labels)

end GroundInitialMainSuccessorData

namespace GroundInitialMainSuccessorData
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {C D rD Labels K : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
variable (sourceTime : source.cutoff ∈ K)
include certificate pairing unions powers separation infinite hK conditions sourceTime

theorem compression_limit_mem : certificate.compression.born.births.limit ∈ K :=
  conditions.compressionStamp_limit_mem pairing unions powers separation infinite hK
    certificate.compression.born.births.times sourceTime certificate.compression.born.births.stamps_ground

theorem external_limit_mem : certificate.births.limit ∈ K :=
  conditions.compressionStamp_limit_mem pairing unions powers separation infinite hK
    certificate.births.times
    (certificate.compression_limit_mem pairing unions powers separation infinite hK conditions sourceTime)
    certificate.births.stamps_ground

end GroundInitialMainSuccessorData

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundCompressionFiniteFieldGraphs
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
variable {base old C Q qlt original : ZFSet.{u}}
variable (births : GroundCompressionBirthData M state.data I Sources Reps G m one T data base old)
variable (heights : GroundCompressionHeightData M state.data I Sources Reps G m one T data P0 C Q qlt original)

theorem prefixTerminalField_ground (j : Fin 5) : state.prefixTerminalField data births heights j ∈ M.sets :=
  Fin.cases (data.ground 0) (Fin.cases (data.ground 1) (Fin.cases (data.ground 2)
    (Fin.cases births.birth_ground (fun _ => heights.height_ground)))) j

theorem exists_prefixFiniteGraphs
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets) :
    ∃ graphs : Fin 5 → ZFSet.{u}, (∀ j, graphs j ∈ M.sets) ∧
      (∀ j, FunctionGraphOn ZFSet.omega (graphs j)) ∧
      ∀ j n y, ZFSet.pair (natSetCode n) y ∈ graphs j ↔
        y = state.prefixFiniteField data births heights j n := by
  have hOmega := M.omega_mem separation infinite
  obtain ⟨history, hHistory, _, entries, _, _⟩ := state.exists_groundHistory
    pairing unions powers separation collection infinite hI hSources hReps hG hT
  obtain ⟨Ps, hPs, pFunc, pEntries⟩ := M.exists_groundStateFieldFamily
    pairing separation collection hOmega hHistory (state.data.iterate M I Sources Reps G T) entries 0
  obtain ⟨Rs, hRs, rFunc, rEntries⟩ := M.exists_groundStateFieldFamily
    pairing separation collection hOmega hHistory (state.data.iterate M I Sources Reps G T) entries 1
  obtain ⟨Ms, hMs, mFunc, mEntries⟩ := M.exists_groundStateFieldFamily
    pairing separation collection hOmega hHistory (state.data.iterate M I Sources Reps G T) entries 2
  let sources : Fin 5 → ZFSet.{u} := Fin.cases Ps (Fin.cases Rs (Fin.cases Ms
    (Fin.cases births.family (fun _ => heights.family))))
  have ground : ∀ j, sources j ∈ M.sets := Fin.cases hPs (Fin.cases hRs (Fin.cases hMs
    (Fin.cases births.family_ground (fun _ => heights.family_ground))))
  have functions : ∀ j, FunctionGraphOn ZFSet.omega (sources j) := Fin.cases pFunc
    (Fin.cases rFunc (Fin.cases mFunc (Fin.cases births.family_function (fun _ => heights.function))))
  refine ⟨fun j => naturalFamilyShift (sources j),
    fun j => M.naturalFamilyShift_mem pairing unions powers separation infinite (ground j),
    fun j => naturalFamilyShift_function (functions j), ?_⟩
  intro j n y
  rw [naturalFamilyShift_entries]
  exact Fin.cases (pEntries (n + 1) y) (Fin.cases (rEntries (n + 1) y)
    (Fin.cases (mEntries (n + 1) y) (Fin.cases (births.family_entries (n + 1) y)
      (fun _ => heights.function.natValue_entry_iff (n + 1) y)))) j

end PartitionPilot.Forcing.GroundCompressionState

end

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

namespace GroundExternalBirthData
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ P0 r0 μ0 A0 oldTimes oldBirth C D rD lo hi seed T0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 oldTimes oldBirth completion)
variable (heights : GroundExternalHeightData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 C D rD lo hi seed completion)
variable (priorFields : GroundChronologyFields M T0)

variable {inv : ZFSet.{u}}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (action : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
variable (ordinal : ordinalSetProperty T0) (hOld : oldTimes ∈ T0)
include data group action pairing unions powers separation infinite hG hP0

include ordinal hOld in
theorem groundChronologyFields_values (prior : GroundChronologicalHistory M T0 C D rD)
    (agreement : ∀ j s, s ∈ T0 → priorFields.value j s = prior.fieldValue j s)
    (j : Fin 5) {s : ZFSet.{u}} (hs : s ∈ insert births.limit births.limit) :
    (births.groundChronologyFields heights priorFields data group action pairing unions powers separation infinite hG hP0 ordinal hOld).value j s =
      (births.chronologyFields heights prior).fieldValue j s := by
  have field : (births.chronologyFields heights prior).fieldValue j =
      compressionPrefixValue oldTimes births.limit (prior.fieldValue j)
        (births.cutoffField heights j) (births.terminalField heights j) :=
    Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))) j
  have oldEntries : ∀ t, t ∈ oldTimes ∨ t = oldTimes → ∀ y,
      ZFSet.pair t y ∈ priorFields.graph j ↔ y = prior.fieldValue j t := by
    intro t before y
    have ht : t ∈ T0 := before.elim (fun h => ordinal.1 oldTimes hOld t h) (fun h => h.symm ▸ hOld)
    constructor
    · intro entry
      exact (priorFields.value_eq_of_entry j entry).symm.trans (agreement j t ht)
    · intro equal
      rw [← agreement j t ht] at equal
      exact equal.symm ▸ priorFields.value_entry j ht
  apply GroundChronologyFields.value_eq_of_entry
  change ZFSet.pair s ((births.chronologyFields heights prior).fieldValue j s) ∈
    compressionPrefixGraph oldTimes births.limit (priorFields.graph j)
      (births.cutoffFieldFamily heights j) births.stamps (births.terminalField heights j)
  exact (compressionPrefixGraph_exact births.times (prior.fieldValue j) (births.cutoffField heights j)
    oldEntries (births.cutoffFieldFamily_spec heights data group action pairing unions powers separation infinite hG hP0 j).2.2 s _).2
      ⟨hs,congrFun field s⟩

end GroundExternalBirthData




end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {T C D rD : ZFSet.{u}}

theorem GroundChronologicalHistory.fieldValue_rank_lt
    (history : GroundChronologicalHistory M T C D rD)
    {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (times : ZFSet.rank T < o) (columns : ZFSet.rank C < o)
    (coordinates : ZFSet.rank D < o) {s : ZFSet.{u}} (hs : s ∈ T)
    (points : ZFSet.rank (history.space s) < o) (j : Fin 5) :
    ZFSet.rank (history.fieldValue j s) < o := by
  have meet := history.meet_order s hs
  have pp := rank_product_lt limit points points
  have order := (ZFSet.rank_mono meet.order.relation).trans_lt pp
  have operation := rank_functionGraph_lt limit meet.operation pp points
  have birth := rank_functionGraph_lt limit (history.birth_function s hs) points times
  have height := rank_functionGraph_lt limit (history.strict_height s hs).function points
    (rank_product_lt limit columns coordinates)
  exact Fin.cases points (Fin.cases order (Fin.cases operation
    (Fin.cases birth (Fin.cases height (fun i => Fin.elim0 i))))) j

namespace GroundChronologyFields
variable (fields : GroundChronologyFields M T)

theorem graph_rank_lt_of_history
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    (hT : T ∈ K) (history : GroundChronologicalHistory M T C D rD)
    (agreement : ∀ j s, s ∈ T → fields.value j s = history.fieldValue j s)
    (points : ∀ s ∈ T, ZFSet.rank (history.space s) < ZFSet.rank K)
    (columns : ZFSet.rank C < ZFSet.rank K) (coordinates : ZFSet.rank D < ZFSet.rank K)
    (j : Fin 5) : ZFSet.rank (fields.graph j) < ZFSet.rank K := by
  apply conditions.functionGraphOn_rank_lt pairing unions powers separation collection infinite hK
    hT (fields.graph_ground j) ⟨fields.bound, fields.function j⟩
  intro s hs v entry
  rw [← fields.value_eq_of_entry j entry, agreement j s hs]
  exact history.fieldValue_rank_lt
    (conditions.rank_isLimit pairing unions powers separation infinite hK)
    (ZFSet.rank_lt_of_mem hT) columns coordinates hs (points s hs) j

end GroundChronologyFields

end PartitionPilot.Forcing




namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
variable {base old T0 C Q qlt original : ZFSet.{u}}
variable (births : GroundCompressionBirthData M state.data I Sources Reps G m one T data base old)
variable (heights : GroundCompressionHeightData M state.data I Sources Reps G m one T data P0 C Q qlt original)
variable (priorFields : GroundChronologyFields M T0)
variable (prior : GroundChronologicalHistory M T0 C Q qlt)

theorem prefixGraph_exact
    (ordinal : ordinalSetProperty T0) (hBase : base ∈ T0)
    (agreement : ∀ j s, s ∈ T0 → priorFields.value j s = prior.fieldValue j s)
    {finiteGraphs : Fin 5 → ZFSet.{u}}
    (finiteEntries : ∀ j n y, ZFSet.pair (natSetCode n) y ∈ finiteGraphs j ↔
      y = state.prefixFiniteField data births heights j n)
    (j : Fin 5) (s y : ZFSet.{u}) :
    ZFSet.pair s y ∈ state.prefixGraph data births heights priorFields finiteGraphs j ↔
      s ∈ insert births.limit births.limit ∧
        y = (state.prefixFields data births heights prior).fieldValue j s := by
  have field : (state.prefixFields data births heights prior).fieldValue j =
      compressionPrefixValue base births.limit (prior.fieldValue j)
        (state.prefixFiniteField data births heights j) (state.prefixTerminalField data births heights j) :=
    Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))) j
  rw [field]
  apply compressionPrefixGraph_exact births.times
  · intro t before z
    have ht : t ∈ T0 := before.elim (fun h => ordinal.1 base hBase t h) (fun h => h.symm ▸ hBase)
    constructor
    · intro entry
      exact (priorFields.value_eq_of_entry j entry).symm.trans (agreement j t ht)
    · intro equal
      rw [← agreement j t ht] at equal
      exact equal.symm ▸ priorFields.value_entry j ht
  · exact finiteEntries j

theorem exists_groundPrefixFields
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets)
    (ordinal : ordinalSetProperty T0) (hBase : base ∈ T0)
    (agreement : ∀ j s, s ∈ T0 → priorFields.value j s = prior.fieldValue j s) :
    ∃ fields : GroundChronologyFields M (insert births.limit births.limit),
      fields.code ∈ M.sets ∧ ChronologyCoreCode (insert births.limit births.limit)
        fields.bound C Q qlt fields.graph ∧
      ∀ j s, s ∈ insert births.limit births.limit →
        fields.value j s = (state.prefixFields data births heights prior).fieldValue j s := by
  obtain ⟨finiteGraphs, finiteGround, _, finiteEntries⟩ := state.exists_prefixFiniteGraphs data births heights
    pairing unions powers separation collection infinite hI hSources hReps hG hT
  let graphs := state.prefixGraph data births heights priorFields finiteGraphs
  have ground : ∀ j, graphs j ∈ M.sets := by
    intro j
    exact M.compressionPrefixGraph_mem pairing unions powers separation (M.omega_mem separation infinite)
      (M.transitive births.limit_ground births.times.base_mem_limit) births.limit_ground
      (priorFields.graph_ground j) (finiteGround j) births.stamps_ground
      (state.prefixTerminalField_ground data births heights j)
  have functions : ∀ j, FunctionGraphOn (insert births.limit births.limit) (graphs j) := by
    intro j
    apply compressionPrefixGraph_function births.times (priorFields.value j)
      (state.prefixFiniteField data births heights j)
    · intro s before y
      have hs : s ∈ T0 := before.elim (fun h => ordinal.1 base hBase s h) (fun h => h.symm ▸ hBase)
      exact ⟨fun entry => (priorFields.value_eq_of_entry j entry).symm,
        fun equal => equal.symm ▸ priorFields.value_entry j hs⟩
    · exact finiteEntries j
  let fields := GroundChronologyFields.ofGraphs pairing unions
    (M.insert_mem pairing unions births.limit_ground births.limit_ground) graphs ground functions
  have values : ∀ j s, s ∈ insert births.limit births.limit →
      fields.value j s = (state.prefixFields data births heights prior).fieldValue j s := by
    intro j s hs
    apply fields.value_eq_of_entry
    exact (state.prefixGraph_exact data births heights priorFields prior ordinal hBase agreement
      finiteEntries j s _).2 ⟨hs, rfl⟩
  refine ⟨fields, fields.code_ground pairing, ⟨fields.function, ?_⟩, values⟩
  intro s hs L r μ birth height eL er eμ eb eh
  have eqL := (fields.value_eq_of_entry 0 eL).symm.trans (values 0 s hs)
  have eqr := (fields.value_eq_of_entry 1 er).symm.trans (values 1 s hs)
  have eqμ := (fields.value_eq_of_entry 2 eμ).symm.trans (values 2 s hs)
  have eqb := (fields.value_eq_of_entry 3 eb).symm.trans (values 3 s hs)
  have eqh := (fields.value_eq_of_entry 4 eh).symm.trans (values 4 s hs)
  rw [eqL, eqr, eqμ, eqb, eqh]
  have laws := state.prefixFields_stage_laws data births heights prior
    pairing unions powers separation hI hSources hReps hG hT ordinal hBase hs
  exact ⟨laws.1, laws.2.1, laws.2.2.1, laws.2.2.2.1, laws.2.2.2.2⟩

end PartitionPilot.Forcing.GroundCompressionState



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRankedCompressionFieldsTransport
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
variable {base old T0 C Q qlt original : ZFSet.{u}}
variable (births : GroundCompressionBirthData M state.data I Sources Reps G m one T data base old)
variable (heights : GroundCompressionHeightData M state.data I Sources Reps G m one T data P0 C Q qlt original)
variable (prior : GroundSerializedChronology M T0 C Q qlt)
variable (fields : GroundChronologyFields M (insert births.limit births.limit))
variable (hBase : base ∈ T0)
variable (values : ∀ j s, s ∈ insert births.limit births.limit →
  fields.value j s = (state.prefixFields data births heights prior.toHistory).fieldValue j s)
include values

theorem prefixOldField_value (j : Fin 5) {s : ZFSet.{u}} (oldTime : s ∈ base ∨ s = base) :
    fields.value j s = prior.fields.value j s := by
  have hs : s ∈ insert births.limit births.limit := ZFSet.mem_insert_of_mem _
    ((births.times.mem_limit_iff s).2 (oldTime.elim Or.inl (fun h => Or.inr (Or.inl h))))
  have oldFields := state.prefixFields_old data births heights prior.toHistory oldTime
  exact (values j s hs).trans (Fin.cases oldFields.1 (Fin.cases oldFields.2.1
    (Fin.cases oldFields.2.2.1 (Fin.cases oldFields.2.2.2.1 (Fin.cases oldFields.2.2.2.2 (fun i => Fin.elim0 i))))) j)

include hBase in
theorem prefixOldField_entries (j : Fin 5) {s : ZFSet.{u}} (oldTime : s ∈ base ∨ s = base)
    (y : ZFSet.{u}) :
    ZFSet.pair s y ∈ prior.fields.graph j ↔ ZFSet.pair s y ∈ fields.graph j := by
  have oldIndex : s ∈ T0 := oldTime.elim (fun h => prior.ordinal.1 base hBase s h) (fun h => h.symm ▸ hBase)
  have newIndex : s ∈ insert births.limit births.limit := ZFSet.mem_insert_of_mem _
    ((births.times.mem_limit_iff s).2 (oldTime.elim Or.inl (fun h => Or.inr (Or.inl h))))
  have equal := state.prefixOldField_value data births heights prior fields values j oldTime
  constructor
  · intro entry
    have output := (prior.fields.value_eq_of_entry j entry).symm.trans equal.symm
    exact output.symm ▸ fields.value_entry j newIndex
  · intro entry
    have output := (fields.value_eq_of_entry j entry).symm.trans equal
    exact output.symm ▸ prior.fields.value_entry j oldIndex

end PartitionPilot.Forcing.GroundCompressionState




namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
variable {base old T0 C Q qlt original : ZFSet.{u}}
variable (births : GroundCompressionBirthData M state.data I Sources Reps G m one T data base old)
variable (heights : GroundCompressionHeightData M state.data I Sources Reps G m one T data P0 C Q qlt original)
variable (prior : GroundSerializedChronology M T0 C Q qlt)
variable (fields : GroundChronologyFields M (insert births.limit births.limit))
variable (hBase : base ∈ T0)
variable (values : ∀ j s, s ∈ insert births.limit births.limit →
  fields.value j s = (state.prefixFields data births heights prior.toHistory).fieldValue j s)
include hBase values in
theorem exists_prefixOldRankedWitness {o : Ordinal.{u}} (priorRank : ZFSet.rank prior.code < o) {cutoff t : ZFSet.{u}}
    (oldCutoff : cutoff ∈ base ∨ cutoff = base) (bound : t = cutoff ∨ t ∈ cutoff) :
    ∃ z ∈ M.sets, GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
      (fields.value 0 cutoff) (fields.value 1 cutoff) (fields.value 2 cutoff)
      (fields.value 3 cutoff) t ZFSet.omega z ∧ ZFSet.rank z < o := by
  have hc : cutoff ∈ T0 := oldCutoff.elim
    (fun member => prior.ordinal.1 base hBase cutoff member) (fun equal => equal.symm ▸ hBase)
  have ht : t ∈ T0 := bound.elim (fun equal => equal.symm ▸ hc)
    (fun before => prior.ordinal.1 cutoff hc t before)
  have oldTime : t ∈ base ∨ t = base := by
    rcases bound with equal | before
    · exact equal.symm ▸ oldCutoff
    · apply Or.inl
      rcases oldCutoff with member | equal
      · exact prior.ordinal.2 base hBase cutoff member t before
      · exact equal ▸ before
  have oldSource {s : ZFSet.{u}} (before : s ∈ t) : s ∈ base ∨ s = base := by
    apply Or.inl
    rcases oldTime with member | equal
    · exact prior.ordinal.2 base hBase t member s before
    · exact equal ▸ before
  have code := (prior.layer_code cutoff hc t ht bound _ (prior.layerWitness_entry hc ht bound)).congr_source_entries
    (fun s hs y => state.prefixOldField_entries data births heights prior fields hBase values 0 (oldSource hs) y)
    (fun s hs y => state.prefixOldField_entries data births heights prior fields hBase values 1 (oldSource hs) y)
    (fun s hs y => state.prefixOldField_entries data births heights prior fields hBase values 2 (oldSource hs) y)
  refine ⟨prior.layerWitness cutoff t, prior.layerWitness_ground cutoff t, ?_,
    (prior.layerWitness_rank_lt_code hc ht bound).trans priorRank⟩
  rw [state.prefixOldField_value data births heights prior fields values 0 oldCutoff,
    state.prefixOldField_value data births heights prior fields values 1 oldCutoff,
    state.prefixOldField_value data births heights prior fields values 2 oldCutoff,
    state.prefixOldField_value data births heights prior fields values 3 oldCutoff]
  exact code

end PartitionPilot.Forcing.GroundCompressionState




namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
variable {base old T0 C Q qlt original : ZFSet.{u}}
variable (births : GroundCompressionBirthData M state.data I Sources Reps G m one T data base old)
variable (heights : GroundCompressionHeightData M state.data I Sources Reps G m one T data P0 C Q qlt original)
variable (prior : GroundSerializedChronology M T0 C Q qlt)
variable (fields : GroundChronologyFields M (insert births.limit births.limit))

theorem prefix_rankedRawWitnesses
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets)
    (hBase : base ∈ T0)
    {o : Ordinal.{u}} (limit : Order.IsSuccLimit o) (priorRank : ZFSet.rank prior.code < o)
    (indices : ZFSet.rank state.data.J < o) (tasks : ZFSet.rank I < o)
    (constant : RecursiveTemplateConstancy P0 r0 μ0 state.data)
    (initialDomain : state.data.D = P0) (initialOrder : state.data.rD = r0)
    (initialMeet : state.data.μD = μ0)
    (priorSpace : prior.fields.value 0 base = P0) (priorOrder : prior.fields.value 1 base = r0)
    (priorMeet : prior.fields.value 2 base = μ0) (priorBirth : prior.fields.value 3 base = old)
    (values : ∀ j s, s ∈ insert births.limit births.limit →
      fields.value j s = (state.prefixFields data births heights prior.toHistory).fieldValue j s) :
    ∀ cutoff ∈ insert births.limit births.limit, ∀ t ∈ insert births.limit births.limit,
      t = cutoff ∨ t ∈ cutoff → ∃ z ∈ M.sets,
      GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
        (fields.value 0 cutoff) (fields.value 1 cutoff) (fields.value 2 cutoff)
        (fields.value 3 cutoff) t ZFSet.omega z ∧ ZFSet.rank z < o := by
  have templates : ZFSet.rank P0 < o := by
    rw [← priorSpace]
    exact (prior.fieldValue_rank_lt_code 0 hBase).trans priorRank
  have points : ZFSet.rank state.data.D < o := initialDomain.symm ▸ templates
  have time : ZFSet.rank base < o :=
    ((ZFSet.rank_lt_of_mem hBase).trans_le prior.time_rank_le_code).trans priorRank
  have baseIn : base ∈ insert births.limit births.limit :=
    ZFSet.mem_insert_of_mem _ births.times.base_mem_limit
  have atBase := fun j => state.prefixOldField_value data births heights prior fields values j
    (Or.inr rfl : base ∈ base ∨ base = base)
  have source : ZFSet.pair base P0 ∈ fields.graph 0 ∧ ZFSet.pair base r0 ∈ fields.graph 1 ∧
      ZFSet.pair base μ0 ∈ fields.graph 2 := by
    have first := fields.value_entry 0 baseIn
    have second := fields.value_entry 1 baseIn
    have third := fields.value_entry 2 baseIn
    rw [atBase 0, priorSpace] at first
    rw [atBase 1, priorOrder] at second
    rw [atBase 2, priorMeet] at third
    exact ⟨first, second, third⟩
  have oldWitness (t : ZFSet.{u}) (before : t ∈ base ∨ t = base) :
      ∃ z ∈ M.sets, GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
        state.data.D state.data.rD state.data.μD old t ZFSet.omega z ∧ ZFSet.rank z < o := by
    obtain ⟨z, hz, code, rank⟩ := state.exists_prefixOldRankedWitness data births heights prior fields hBase values priorRank
      (Or.inr rfl : base ∈ base ∨ base = base) before.symm
    rw [atBase 0, atBase 1, atBase 2, atBase 3, priorSpace, priorOrder, priorMeet, priorBirth] at code
    exact ⟨z, hz, initialDomain.symm ▸ initialOrder.symm ▸ initialMeet.symm ▸ code, rank⟩
  have incoming (n : Nat) := state.exists_canonicalIncomingRankedWitness data births
    pairing unions powers separation hI hSources hReps hG hT constant
    (fields.graphFunction 0) (fields.graphFunction 1) (fields.graphFunction 2) source limit points indices templates tasks time n (N := ZFSet.omega)
  have atStamp (n : Nat) :
      fields.value 0 (compressionStamp base n) = (state.data.iterate M I Sources Reps G T (n + 1)).D ∧
      fields.value 1 (compressionStamp base n) = (state.data.iterate M I Sources Reps G T (n + 1)).rD ∧
      fields.value 2 (compressionStamp base n) = (state.data.iterate M I Sources Reps G T (n + 1)).μD ∧
      fields.value 3 (compressionStamp base n) = graphRestriction
        (state.data.iterate M I Sources Reps G T (n + 1)).D births.birth := by
    have hs := ZFSet.mem_insert_of_mem births.limit (births.times.stamp_mem_limit n)
    have exactFields := state.prefixFields_stamp data births heights prior.toHistory n
    exact ⟨(values 0 _ hs).trans exactFields.1, (values 1 _ hs).trans exactFields.2.1,
      (values 2 _ hs).trans exactFields.2.2.1, (values 3 _ hs).trans exactFields.2.2.2.1⟩
  have atLimit : fields.value 0 births.limit = data.fields 0 ∧
      fields.value 1 births.limit = data.fields 1 ∧ fields.value 2 births.limit = data.fields 2 ∧
      fields.value 3 births.limit = births.birth := by
    have hs := ZFSet.mem_insert births.limit births.limit
    have exactFields := state.prefixFields_limit data births heights prior.toHistory
    exact ⟨(values 0 _ hs).trans exactFields.1, (values 1 _ hs).trans exactFields.2.1,
      (values 2 _ hs).trans exactFields.2.2.1, (values 3 _ hs).trans exactFields.2.2.2.1⟩
  have finite (n : Nat) (t : ZFSet.{u}) (bound : t = compressionStamp base n ∨ t ∈ compressionStamp base n) :
      ∃ z ∈ M.sets, GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
        (fields.value 0 (compressionStamp base n)) (fields.value 1 (compressionStamp base n))
        (fields.value 2 (compressionStamp base n)) (fields.value 3 (compressionStamp base n)) t ZFSet.omega z ∧ ZFSet.rank z < o := by
    rw [(atStamp n).1, (atStamp n).2.1, (atStamp n).2.2.1, (atStamp n).2.2.2]
    have cases : (t ∈ base ∨ t = base) ∨ ∃ j, j ≤ n ∧ t = compressionStamp base j := by
      rcases bound with equal | before
      · exact Or.inr ⟨n, Nat.le_refl n, equal⟩
      · rcases (mem_compressionStamp_iff base t n).1 before with old | same | ⟨j, earlier, equal⟩
        · exact Or.inl (Or.inl old)
        · exact Or.inl (Or.inr same)
        · exact Or.inr ⟨j, Nat.le_of_lt earlier, equal⟩
    rcases cases with before | ⟨j, before, rfl⟩
    · obtain ⟨z, hz, code, rank⟩ := oldWitness t before
      exact state.exists_priorWitness_to_finite_rank_lt data births pairing unions powers separation hI hSources hReps hG hT limit
        (n + 1) before hz rank code
    · obtain ⟨z, hz, rank, code⟩ := incoming j
      exact state.exists_birthWitness_to_finite_rank_lt data births pairing unions powers separation hI hSources hReps hG hT limit
        (j + 1) (n + 1) (Nat.add_le_add_right before 1)
        ((compressionStamp_mem_iff base j (j + 1)).2 (Nat.lt_succ_self j)) hz rank code
  have terminal (t : ZFSet.{u}) (bound : t = births.limit ∨ t ∈ births.limit) :
      ∃ z ∈ M.sets, GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
        (fields.value 0 births.limit) (fields.value 1 births.limit)
        (fields.value 2 births.limit) (fields.value 3 births.limit) t ZFSet.omega z ∧ ZFSet.rank z < o := by
    rw [atLimit.1, atLimit.2.1, atLimit.2.2.1, atLimit.2.2.2]
    rcases bound with rfl | before
    · exact state.exists_limitWitness_rank_lt data births pairing limit
    · rcases (births.times.mem_limit_iff t).1 before with old | same | ⟨j, rfl⟩
      · obtain ⟨z, hz, code, rank⟩ := oldWitness t (Or.inl old)
        exact state.exists_priorWitness_to_union_rank_lt data births pairing unions powers separation hI hSources hReps hG hT limit
          (Or.inl old) hz rank code
      · obtain ⟨z, hz, code, rank⟩ := oldWitness t (Or.inr same)
        exact state.exists_priorWitness_to_union_rank_lt data births pairing unions powers separation hI hSources hReps hG hT limit
          (Or.inr same) hz rank code
      · obtain ⟨z, hz, rank, code⟩ := incoming j
        exact state.exists_birthWitness_to_union_rank_lt data births pairing unions powers separation hI hSources hReps hG hT limit
          (j + 1) ((compressionStamp_mem_iff base j (j + 1)).2 (Nat.lt_succ_self j)) hz rank code
  intro cutoff hc t _ bound
  rcases ZFSet.mem_insert_iff.1 hc with rfl | before
  · exact terminal t bound
  · rcases (births.times.mem_limit_iff cutoff).1 before with oldTime | same | ⟨n, rfl⟩
    · exact state.exists_prefixOldRankedWitness data births heights prior fields hBase values priorRank (Or.inl oldTime) bound
    · exact state.exists_prefixOldRankedWitness data births heights prior fields hBase values priorRank (Or.inr same) bound
    · exact finite n t bound

end PartitionPilot.Forcing.GroundCompressionState



namespace PartitionPilot.Forcing.GroundCompressionOrigin
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters C Q qlt original Targets Separators base old T0 : ZFSet.{u}}
variable {history : GroundChronologicalHistory M T0 C Q qlt}
variable (origin : GroundCompressionOrigin M initial P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters)
variable (compression : GroundChronologicalCompression M initial I Sources Reps G m one T τ
  P0 C Q qlt original Targets Separators Filters base old T0 history)
variable (prior : GroundSerializedChronology M T0 C Q qlt)

include origin in
theorem exists_rankedRawCompressionFields
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets) (hBase : base ∈ T0)
    {o : Ordinal.{u}} (limit : Order.IsSuccLimit o) (priorRank : ZFSet.rank prior.code < o)
    (indices : ZFSet.rank initial.J < o) (tasks : ZFSet.rank I < o)
    (constant : RecursiveTemplateConstancy P0 r0 μ0 initial)
    (initialDomain : initial.D = P0) (initialOrder : initial.rD = r0) (initialMeet : initial.μD = μ0)
    (priorSpace : history.space base = P0) (priorOrder : history.order base = r0)
    (priorMeet : history.meetGraph base = μ0) (priorBirth : history.birth base = old)
    (agreement : ∀ j s, s ∈ T0 → prior.fields.value j s = history.fieldValue j s) :
    ∃ fields : GroundChronologyFields M
        (insert compression.born.births.limit compression.born.births.limit),
      fields.code ∈ M.sets ∧
      ChronologyCoreCode (insert compression.born.births.limit compression.born.births.limit)
        fields.bound C Q qlt fields.graph ∧
      (∀ j s, s ∈ insert compression.born.births.limit compression.born.births.limit →
        fields.value j s = compression.history.fieldValue j s) ∧
      (∀ s ∈ insert compression.born.births.limit compression.born.births.limit,
        ∀ t ∈ insert compression.born.births.limit compression.born.births.limit,
        t = s ∨ t ∈ s → ∃ z ∈ M.sets, ZFSet.rank z < o ∧
          GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
            (fields.value 0 s) (fields.value 1 s) (fields.value 2 s) (fields.value 3 s) t ZFSet.omega z) := by
  obtain ⟨seed, state, equal⟩ := origin
  cases equal
  let data := compression.born.profiled.heighted.completion.algebra.union
  let births := compression.born.births
  let heights := compression.born.profiled.heighted.heights
  obtain ⟨fields, ground, core, values⟩ := state.exists_groundPrefixFields data births heights
    prior.fields prior.toHistory pairing unions powers separation collection infinite
    hI hSources hReps hG hT prior.ordinal hBase
      (fun j _ _ => Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))) j)
  have ranked := state.prefix_rankedRawWitnesses data births heights prior fields
    pairing unions powers separation hI hSources hReps hG hT hBase limit priorRank indices tasks
    constant initialDomain initialOrder initialMeet
    ((agreement 0 base hBase).trans priorSpace) ((agreement 1 base hBase).trans priorOrder)
    ((agreement 2 base hBase).trans priorMeet) ((agreement 3 base hBase).trans priorBirth) values
  refine ⟨fields, ground, core, ?_, ?_⟩
  · intro j s hs
    rw [values j s hs]
    have oldValue (a : ZFSet.{u}) (before : a ∈ base ∨ a = base) :
        (state.prefixFields data births heights prior.toHistory).fieldValue j a =
          compression.history.fieldValue j a := by
      have ha : a ∈ T0 := before.elim (fun h => prior.ordinal.1 base hBase a h) (fun h => h.symm ▸ hBase)
      have left := state.prefixFields_old data births heights prior.toHistory before
      have right := compression.old_values a before
      have eLeft : (state.prefixFields data births heights prior.toHistory).fieldValue j a =
          prior.fields.value j a :=
        Fin.cases left.1 (Fin.cases left.2.1 (Fin.cases left.2.2.1
          (Fin.cases left.2.2.2.1 (Fin.cases left.2.2.2.2 (fun i => Fin.elim0 i))))) j
      have eRight : compression.history.fieldValue j a = history.fieldValue j a :=
        Fin.cases right.1 (Fin.cases right.2.1 (Fin.cases right.2.2.1
          (Fin.cases right.2.2.2.1 (Fin.cases right.2.2.2.2 (fun i => Fin.elim0 i))))) j
      exact eLeft.trans ((agreement j a ha).trans eRight.symm)
    rcases ZFSet.mem_insert_iff.1 hs with rfl | hs
    · have left := state.prefixFields_limit data births heights prior.toHistory
      have right := compression.limit_values
      exact Fin.cases (left.1.trans right.1.symm)
        (Fin.cases (left.2.1.trans right.2.1.symm) (Fin.cases (left.2.2.1.trans right.2.2.1.symm)
          (Fin.cases (left.2.2.2.1.trans right.2.2.2.1.symm)
            (Fin.cases (left.2.2.2.2.trans right.2.2.2.2.symm) (fun i => Fin.elim0 i))))) j
    · rcases (births.times.mem_limit_iff s).1 hs with before | equal | ⟨n, rfl⟩
      · exact oldValue s (Or.inl before)
      · exact oldValue s (Or.inr equal)
      · have left := state.prefixFields_stamp data births heights prior.toHistory n
        have right := compression.stamp_values n
        exact Fin.cases (left.1.trans right.1.symm)
          (Fin.cases (left.2.1.trans right.2.1.symm) (Fin.cases (left.2.2.1.trans right.2.2.1.symm)
            (Fin.cases (left.2.2.2.1.trans right.2.2.2.1.symm)
              (Fin.cases (left.2.2.2.2.trans right.2.2.2.2.symm) (fun i => Fin.elim0 i))))) j

  · intro s hs t ht earlier
    obtain ⟨z, hz, code, rank⟩ := ranked s hs t ht earlier
    exact ⟨z, hz, rank, code⟩

end PartitionPilot.Forcing.GroundCompressionOrigin

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundExternalSlotCopies
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetFormula SetRealization Compression Compression.RecursiveMaps.CosetGeometry
universe u

namespace GroundExternalGeometryInputs
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets)
local notation "family" => completion.externalFamily group oldAction data.original
local notation "action" => completion.algebra.union.action.toOrderAction group completion.algebra.union.meet
local notation "s" => completion.externalFamilyGroupPresentation group oldAction data.original
  pairing unions powers separation infinite hG data.words.letters_ground
local notation "q" => data.externalPointPresentation group oldAction pairing unions powers separation infinite hG
local notation "vpres" => data.externalStarVertexPresentation group oldAction pairing unions powers separation infinite hG
local notation "Index" => ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "U" => completion.algebra.union.fields 0
local notation "B" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "vcode" => completion.externalFamilyVertexCode group oldAction data.original
local notation "R(" j ")" => completion.externalSlotCopyRelation P0 r0 μ0 A0 j
include data group oldAction pairing unions powers separation infinite hG

theorem externalSlotCopyRelation_ground (hP0 : P0 ∈ M.sets) {j : ZFSet.{u}} (hj : j ∈ M.sets) :
    R(j) ∈ M.sets := by
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  have localGround := data.localTileGroundInputs group oldAction pairing unions powers separation infinite hG hP0
  exact M.externalSlotCopyGraph_mem pairing unions powers separation
    (data.externalStarCarriers_ground pairing unions powers separation hG).1 data.group.carrier_mem
    data.words.requests_ground (completion.algebra.union.ground 0) geometry.carrier_ground
    geometry.action_ground localGround.2.2.2.1 hj

theorem externalSlotCopyRelation_entry :
    letI := group.toGroup
    ∀ (w : External (SetMembers G) (family).Letters) (r : Index)
      (i : Option ((family).Child r)) (x : SetMembers U) (y : (family).Node (action)),
      ZFSet.pair (ZFSet.pair ((vpres).encode (.inr (w, r))) (SetMembers.raw x)) ((q).encode y) ∈ R(vcode r i) ↔
        ((family).placedTile (action) w r).toFun (((family).flatVertex r i).toFun x) = y := by
  let := group.toGroup
  intro w r i x y
  have sc := completion.externalFamilyGroupPresentation_carrier group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground
  have qc := data.externalPointPresentation_carrier group oldAction pairing unions powers separation infinite hG
  have vc := (data.externalStarPresentations_carriers group oldAction pairing unions powers separation infinite hG).1
  have acted := (data.externalGeometry_entries group oldAction pairing unions powers separation infinite hG).2.2.1
  rw [GroundCompressionCompletion.externalSlotCopyRelation, triple_mem_externalSlotCopyGraph]
  constructor
  · rintro ⟨_, _, _, w', _, r', _, z, hz, equal, copied, moved⟩
    change ZFSet.pair (natSetCode 1) (ZFSet.pair ((s).encode w) (externalRequestIndexCode r)) =
      ZFSet.pair (natSetCode 1) (ZFSet.pair w' r') at equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 (ZFSet.pair_inj.1 equal).2
    obtain ⟨z, rfl⟩ := ((q).mem_carrier z).1 (qc.symm ▸ hz)
    have copied' := (data.localTileVertexImages_entry_iff group oldAction pairing unions powers separation infinite hG
      r i x z).1 copied
    have moved' := (acted w z y).1 moved
    rw [← copied', ← (family).flatVertex_copy, (family).translate_tile, mul_one] at moved'
    exact moved'
  · intro equal
    refine ⟨vc ▸ (vpres).encode_mem _, SetMembers.raw_mem x, qc ▸ (q).encode_mem _,
      (s).encode w, sc ▸ (s).encode_mem _, externalRequestIndexCode r,
      (externalRequestPresentation I P0 (externalRectangles P0 G r0 μ0 A0)).encode_mem _,
      (q).encode (((family).placedTile (action) 1 r).toFun (((family).flatVertex r i).toFun x)),
      qc ▸ (q).encode_mem _, rfl, ?_, ?_⟩
    · apply (data.localTileVertexImages_entry_iff group oldAction pairing unions powers separation infinite hG r i x _).2
      exact ((family).flatVertex_copy (action) 1 r i x).symm
    · apply (acted w _ _).2
      rw [(family).translate_tile, mul_one]
      exact equal

theorem externalSlotCopySection_eq :
    letI := group.toGroup
    ∀ (w : External (SetMembers G) (family).Letters) (r : Index) (i : Option ((family).Child r)),
      indexedRelationSection U B R(vcode r i) ((vpres).encode (.inr (w, r))) =
        completion.externalCopyGraph P0 r0 μ0 A0 ((s).encode ((family).flatWord w r i)) := by
  let := group.toGroup
  intro w r i
  have qc := data.externalPointPresentation_carrier group oldAction pairing unions powers separation infinite hG
  rw [data.externalCopyGraph_eq_graph group oldAction pairing unions powers separation infinite hG]
  apply ZFSet.ext
  intro z
  constructor
  · intro entry
    obtain ⟨x, hx, y, hy, rfl, copied⟩ := (mem_indexedRelationSection _ _ _ _ _).1 entry
    obtain ⟨y, rfl⟩ := ((q).mem_carrier y).1 (qc.symm ▸ hy)
    let x' := SetMembers.ofMem x hx
    have image := (data.externalSlotCopyRelation_entry group oldAction pairing unions powers separation infinite hG
      w r i x' y).1 (by simpa only [x', SetMembers.raw_ofMem] using copied)
    rw [(family).flatVertex_copy] at image
    have result := ((SetMembers.presentation U).pair_mem_graph (q) _ x' y).2 image
    simpa only [SetMembers.presentation, x', SetMembers.raw_ofMem] using result
  · intro entry
    obtain ⟨x, rfl⟩ := ((SetMembers.presentation U).mem_graph (q) _ z).1 entry
    apply (pair_mem_indexedRelationSection _ _ _ _ _ _).2
    refine ⟨SetMembers.raw_mem x, qc ▸ (q).encode_mem _, ?_⟩
    exact (data.externalSlotCopyRelation_entry group oldAction pairing unions powers separation infinite hG
      w r i x _).2 ((family).flatVertex_copy (action) w r i x)

theorem externalSlotCopyMaps_spec (hP0 : P0 ∈ M.sets) {Active j : ZFSet.{u}}
    (hActive : Active ∈ M.sets) (hj : j ∈ M.sets) :
    completion.externalSlotCopyMaps P0 r0 μ0 A0 Active j ∈ M.sets ∧
      ZFSet.IsFunc Active (M.groundRelations U B) (completion.externalSlotCopyMaps P0 r0 μ0 A0 Active j) ∧
      ∀ v e, ZFSet.pair v e ∈ completion.externalSlotCopyMaps P0 r0 μ0 A0 Active j ↔
        v ∈ Active ∧ e = indexedRelationSection U B R(j) v := by
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  exact M.indexedRelationSections_spec pairing unions powers separation hActive
    (completion.algebra.union.ground 0) geometry.carrier_ground
    (data.externalSlotCopyRelation_ground group oldAction pairing unions powers separation infinite hG hP0 hj)

end GroundExternalGeometryInputs

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_ExternalBirthLayerSeparation
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace GroundExternalBirthData
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ P0 r0 μ0 A0 oldTimes oldBirth : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ P0 r0 μ0 A0 oldTimes oldBirth completion)
local notation "U" => completion.algebra.union.fields 0
local notation "B" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "V" => M.externalStarVertices G (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0))
  (externalRequestCarrier I P0 (externalRectangles P0 G r0 μ0 A0)) m one
local notation "owner" => completion.externalStarOwner P0 r0 μ0 A0

theorem mem_layerFiber (k : Nat) (x : ZFSet.{u}) :
    x ∈ births.layerFiber k ↔ x ∈ B ∧ ZFSet.pair x (compressionStamp oldTimes k) ∈ births.birth :=
  mem_layerBirthFiber _ _ _ _

theorem layerFiber_level {k : Nat} {x : ZFSet.{u}} (hx : x ∈ births.layerFiber k) :
    ZFSet.pair x (natSetCode k) ∈ completion.externalOwnerLevels P0 r0 μ0 A0 :=
  ((births.stamp_fiber k x).1 ((births.mem_layerFiber k x).1 hx).2).2

theorem layerOwners_cases {k : Nat} {v : ZFSet.{u}} (hv : v ∈ births.layerOwners k) :
    v ∈ V ∧ ∃ x ∈ births.layerFiber k, ZFSet.pair x v ∈ owner :=
  (mem_relationImage _ _ _ _).1 hv

variable {inv : ZFSet.{u}}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
include data group oldAction pairing unions powers separation infinite hG hP0

theorem layer_fields_ground (k : Nat) :
    births.layerFiber k ∈ M.sets ∧ births.layerOwners k ∈ M.sets ∧
      births.layerComponents k ∈ M.sets ∧ births.layerIndices k ∈ M.sets ∧
      births.layerMaps k ∈ M.sets ∧ M.groundRelations U B ∈ M.sets := by
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  have owners := data.externalStarOwner_ground_function group oldAction pairing unions powers separation infinite hG hP0
  have vertices := (data.externalStarCarriers_ground pairing unions powers separation hG).1
  have fiber := M.layerBirthFiber_mem separation geometry.carrier_ground births.birth_ground
    (M.transitive births.limit_ground (births.times.stamp_mem_limit k))
  have active := M.relationImage_mem separation fiber vertices owners.1
  have components := M.graphRestriction_mem unions separation fiber owners.1
  have indices := M.constantFamilyGraph_mem pairing unions powers separation active
    (M.transitive births.limit_ground births.times.base_mem_limit)
  have maps := data.externalSlotCopyMaps_spec group oldAction pairing unions powers separation infinite hG hP0
    active (M.natSetCode_mem separation infinite (k % 3))
  exact ⟨fiber, active, components, indices, maps.1,
    M.groundRelations_mem pairing unions powers separation (completion.algebra.union.ground 0) geometry.carrier_ground⟩

theorem layerComponents_function (k : Nat) :
    ZFSet.IsFunc (births.layerFiber k) (births.layerOwners k) (births.layerComponents k) := by
  have ownerCode := (data.externalStarOwner_ground_function group oldAction pairing unions powers separation infinite hG hP0).2
  have restricted := (show FunctionGraphOn B owner from ⟨V, ownerCode⟩).restrict
    (fun x hx => (births.mem_layerFiber k x).1 hx |>.1)
  apply isFunc_retarget_of_entries restricted.to_isFunc
  intro x v entry
  obtain ⟨owned, hx⟩ := pair_mem_graphRestriction.1 entry
  exact (mem_relationImage _ _ _ _).2
    ⟨(ZFSet.pair_mem_prod.1 (ownerCode.1 owned)).2, x, hx, owned⟩

omit data group oldAction pairing unions powers separation infinite hG hP0 in
theorem layerIndices_function (k : Nat) :
    ZFSet.IsFunc (births.layerOwners k) (compressionStamp oldTimes k) (births.layerIndices k) := by
  apply isFunc_retarget_of_entries (constantFamilyGraph_function (births.layerOwners k) oldTimes)
  intro v t entry
  rw [((pair_mem_constantFamilyGraph _ _ _ _).1 entry).2]
  exact compressionStamp_base_mem oldTimes k

theorem layerMaps_spec (k : Nat) :
    ZFSet.IsFunc (births.layerOwners k) (M.groundRelations U B) (births.layerMaps k) ∧
      ∀ v e, ZFSet.pair v e ∈ births.layerMaps k ↔ v ∈ births.layerOwners k ∧
        e = indexedRelationSection U B (completion.externalSlotCopyRelation P0 r0 μ0 A0 (natSetCode (k % 3))) v := by
  exact (data.externalSlotCopyMaps_spec group oldAction pairing unions powers separation infinite hG hP0
    (births.layer_fields_ground data group oldAction pairing unions powers separation infinite hG hP0 k).2.1
    (M.natSetCode_mem separation infinite (k % 3))).2

theorem layerWitness_ground (k : Nat) : births.layerWitness k ∈ M.sets := by
  have ground := births.layer_fields_ground data group oldAction pairing unions powers separation infinite hG hP0 k
  exact M.separatedLayerWitness_mem pairing unions ground.2.1 ground.2.2.2.1
    ground.2.2.2.2.1 ground.2.2.2.2.2 ground.2.2.1 ground.1

end GroundExternalBirthData
end PartitionPilot.Forcing




namespace PartitionPilot.Forcing.GroundExternalBirthData
open SetFormula SetRealization Compression Compression.RecursiveMaps.CosetGeometry
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 oldTimes oldBirth : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ P0 r0 μ0 A0 oldTimes oldBirth completion)
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
local notation "family" => completion.externalFamily group oldAction data.original
local notation "s" => completion.externalFamilyGroupPresentation group oldAction data.original
  pairing unions powers separation infinite hG data.words.letters_ground
local notation "vpres" => data.externalStarVertexPresentation group oldAction pairing unions powers separation infinite hG
local notation "U" => completion.algebra.union.fields 0
local notation "B" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "P" => completion.externalSeedCarrier P0 r0 μ0 A0
local notation "owner" => completion.externalStarOwner P0 r0 μ0 A0
include births data group oldAction pairing unions powers separation infinite hG hP0

theorem layerMaps_copy (k : Nat) {x v e : ZFSet.{u}}
    (hx : x ∈ births.layerFiber k) (owned : ZFSet.pair x v ∈ owner)
    (mapEntry : ZFSet.pair v e ∈ births.layerMaps k) :
    letI := group.toGroup
    ∃ w r, v = (vpres).encode (.inr (w, r)) ∧
      e = completion.externalCopyGraph P0 r0 μ0 A0
        ((s).encode ((family).flatWord w r (data.externalBirthCopyVertex group oldAction k r))) ∧
      x ∈ relationImage U B e := by
  let := group.toGroup
  have level := births.layerFiber_level hx
  obtain ⟨w, r, actualOwner, covered⟩ := data.externalBirthCopy_witness group oldAction
    pairing unions powers separation infinite hG hP0 k level
  have ownerCode : FunctionGraphOn B owner :=
    ⟨_, (data.externalStarOwner_ground_function group oldAction pairing unions powers separation infinite hG hP0).2⟩
  have same := ownerCode.unique owned actualOwner
  obtain ⟨n, _, rank⟩ := data.externalBirthCopy_level_slot group oldAction
    pairing unions powers separation infinite hG hP0 w r k actualOwner level
  let i := data.externalBirthCopyVertex group oldAction k r
  have slot : ((family).request r).vertexSlot i = k % 3 := by
    rw [rank, depthSlotIndex, Nat.add_mod]
    simp only [i, Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod, Nat.zero_add,
      Nat.mod_eq_of_lt (((family).request r).vertexSlot_lt_three (data.externalBirthCopyVertex group oldAction k r))]
  have literal : completion.externalFamilyVertexCode group oldAction data.original r i = natSetCode (k % 3) :=
    (completion.externalFamilyVertexCode_eq_slot group oldAction data.original r i).trans
      (congrArg natSetCode slot)
  have mapEq := ((births.layerMaps_spec data group oldAction pairing unions powers separation infinite hG hP0 k).2 v e).1 mapEntry |>.2
  have sectionEq := data.externalSlotCopySection_eq group oldAction pairing unions powers separation infinite hG w r i
  rw [literal, ← same] at sectionEq
  have actual := mapEq.trans sectionEq
  exact ⟨w, r, same, actual, actual.symm ▸ covered⟩

theorem layerMaps_embedding (k : Nat) {v e : ZFSet.{u}}
    (mapEntry : ZFSet.pair v e ∈ births.layerMaps k) :
    MeetEmbeddingCode U B (completion.algebra.union.fields 1) (completion.externalPointOrder P0 r0 μ0 A0)
      (completion.algebra.union.fields 2) (completion.externalPointMeet P0 r0 μ0 A0) e := by
  let := group.toGroup
  have active := ((births.layerMaps_spec data group oldAction pairing unions powers separation infinite hG hP0 k).2 v e).1 mapEntry |>.1
  obtain ⟨_, x, hx, owned⟩ := births.layerOwners_cases active
  obtain ⟨w, r, _, rfl, _⟩ := births.layerMaps_copy data group oldAction pairing unions powers separation infinite hG hP0 k hx owned mapEntry
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  have sc := completion.externalFamilyGroupPresentation_carrier group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground
  exact geometry.copies _ (sc ▸ (s).encode_mem _)

theorem layerMaps_outputs_cutoff (k n : Nat) (before : k ≤ n) {v e u y : ZFSet.{u}}
    (mapEntry : ZFSet.pair v e ∈ births.layerMaps k) (copied : ZFSet.pair u y ∈ e) :
    y ∈ births.cutoff n := by
  let := group.toGroup
  have active := ((births.layerMaps_spec data group oldAction pairing unions powers separation infinite hG hP0 k).2 v e).1 mapEntry |>.1
  obtain ⟨_, x, hx, owned⟩ := births.layerOwners_cases active
  obtain ⟨w, r, same, actual, _⟩ := births.layerMaps_copy data group oldAction pairing unions powers separation infinite hG hP0 k hx owned mapEntry
  rcases data.externalBirthCopy_level_bound group oldAction pairing unions powers separation infinite hG hP0
    w r k (same ▸ owned) (births.layerFiber_level hx) (actual ▸ copied) with old | ⟨l, bound, level⟩
  · exact births.cutoff_old n old
  · have levelCode := (data.externalOwnerLevels_ground_function group oldAction pairing unions powers separation infinite hG hP0).2
    have fresh := (mem_ownerFresh P B y).1 (ZFSet.pair_mem_prod.1 (levelCode.1 level)).1
    apply (mem_ownerLevelPrefix _ _ _ _ _).2
    refine Or.inr ⟨fresh.1, fresh.2, natSetCode l, natSetCode_mem_omega l, level, ?_⟩
    rcases Nat.lt_or_eq_of_le (Nat.le_trans bound before) with less | same
    · exact Or.inr ((natSetCode_mem_iff _ _).2 less)
    · exact Or.inl (congrArg natSetCode same)

theorem layerMaps_cutoff_embedding (k n : Nat) (before : k ≤ n) {v e : ZFSet.{u}}
    (mapEntry : ZFSet.pair v e ∈ births.layerMaps k) :
    MeetEmbeddingCode U (births.cutoff n) (completion.algebra.union.fields 1) (births.cutoffOrder n)
      (completion.algebra.union.fields 2) (births.cutoffMeet n) e :=
  (births.layerMaps_embedding data group oldAction pairing unions powers separation infinite hG hP0 k mapEntry).restrictTarget
    (fun _ _ copied => births.layerMaps_outputs_cutoff data group oldAction pairing unions powers separation infinite hG hP0 k n before mapEntry copied)

end PartitionPilot.Forcing.GroundExternalBirthData




namespace PartitionPilot.Forcing.GroundExternalBirthData
open SetFormula SetRealization Compression Compression.RecursiveMaps.CosetGeometry
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 oldTimes oldBirth : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ P0 r0 μ0 A0 oldTimes oldBirth completion)
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
local notation "B" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "P" => completion.externalSeedCarrier P0 r0 μ0 A0
include births data group oldAction pairing unions powers separation infinite hG hP0

omit data group oldAction pairing unions powers separation infinite hG hP0 in
theorem layerFiber_cutoff (k n : Nat) (before : k ≤ n) :
    births.layerFiber k = layerBirthFiber (births.cutoff n) (births.cutoffBirth n) (compressionStamp oldTimes k) := by
  apply ZFSet.ext
  intro x
  rw [births.mem_layerFiber, mem_layerBirthFiber]
  constructor
  · rintro ⟨hx, entry⟩
    have fresh := (births.stamp_fiber k x).1 entry
    have hxCut : x ∈ births.cutoff n := by
      apply (mem_ownerLevelPrefix _ _ _ _ _).2
      refine Or.inr ⟨hx, ((mem_ownerFresh P B x).1 fresh.1).2,
        natSetCode k, natSetCode_mem_omega k, fresh.2, ?_⟩
      rcases Nat.lt_or_eq_of_le before with less | same
      · exact Or.inr ((natSetCode_mem_iff _ _).2 less)
      · exact Or.inl (congrArg natSetCode same)
    exact ⟨hxCut, pair_mem_graphRestriction.2 ⟨entry, hxCut⟩⟩
  · rintro ⟨hx, entry⟩
    exact ⟨births.cutoff_subset n hx, (pair_mem_graphRestriction.1 entry).1⟩

theorem layerComponents_earlier_meet (k : Nat) {x y v w : ZFSet.{u}}
    (hx : x ∈ births.layerFiber k) (hy : y ∈ births.layerFiber k)
    (first : ZFSet.pair x v ∈ births.layerComponents k)
    (second : ZFSet.pair y w ∈ births.layerComponents k) (different : v ≠ w) :
    ∃ z a, ZFSet.pair (ZFSet.pair x y) z ∈ completion.externalPointMeet P0 r0 μ0 A0 ∧
      ZFSet.pair z a ∈ births.birth ∧ a ∈ compressionStamp oldTimes k := by
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  have bounds := ZFSet.pair_mem_prod.2
    ⟨((births.mem_layerFiber k x).1 hx).1, ((births.mem_layerFiber k y).1 hy).1⟩
  obtain ⟨z, meetEntry, _⟩ := geometry.meet.operation.2 (ZFSet.pair x y) bounds
  have hz := (ZFSet.pair_mem_prod.1 (geometry.meet.operation.1 meetEntry)).2
  obtain ⟨a, born, _⟩ := births.function.2 z hz
  have earlier := data.externalOwnerLevels_meet_old_or_lower group oldAction pairing unions powers separation infinite hG hP0
    (pair_mem_graphRestriction.1 first).1 (pair_mem_graphRestriction.1 second).1 different
    (births.layerFiber_level hx) (births.layerFiber_level hy) meetEntry
  refine ⟨z, a, meetEntry, born, ?_⟩
  apply ownerBirthGraph_earlier_of_level births.seed_function
    (data.externalOwnerLevels_ground_function group oldAction pairing unions powers separation infinite hG hP0).2
    births.times.ownerStampCode ?_ ((births.times.entries k _).2 rfl) born earlier
  intro u b j t entry stamp
  rw [(births.times.entries j t).1 stamp]
  exact births.old_before entry j

end PartitionPilot.Forcing.GroundExternalBirthData

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundExternalLayerWitnessRanks
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.GroundExternalBirthData
open SetFormula SetRealization Compression Compression.RecursiveMaps.CosetGeometry
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 oldTimes oldBirth : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ P0 r0 μ0 A0 oldTimes oldBirth completion)
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
local notation "U" => completion.algebra.union.fields 0
local notation "B" => completion.externalPointCarrier P0 r0 μ0 A0
include births data group oldAction pairing unions powers separation infinite hG hP0

variable {HQs Hrs Hμs HTime : ZFSet.{u}}
variable (historySpaces : FunctionGraphOn HTime HQs)
variable (historyOrders : FunctionGraphOn HTime Hrs)
variable (historyMeets : FunctionGraphOn HTime Hμs)
variable (source : ZFSet.pair oldTimes (completion.algebra.union.fields 0) ∈ HQs ∧
  ZFSet.pair oldTimes (completion.algebra.union.fields 1) ∈ Hrs ∧
  ZFSet.pair oldTimes (completion.algebra.union.fields 2) ∈ Hμs)

include historySpaces historyOrders historyMeets source

theorem layerSeparatedCode (k : Nat) :
    SeparatedLayerCode HQs Hrs Hμs B (completion.externalPointOrder P0 r0 μ0 A0)
      (completion.externalPointMeet P0 r0 μ0 A0) births.birth (compressionStamp oldTimes k)
      (births.layerOwners k) (births.layerIndices k) (births.layerMaps k)
      (M.groundRelations U B) (births.layerComponents k) (births.layerFiber k) := by
  refine ⟨births.layerIndices_function k,
    (births.layerMaps_spec data group oldAction pairing unions powers separation infinite hG hP0 k).1,
    rfl, births.layerComponents_function data group oldAction pairing unions powers separation infinite hG hP0 k,
    ?_, ?_, ?_⟩
  · intro i _ t _ e Q R V indexEntry mapEntry spaceEntry orderEntry meetEntry
    obtain rfl := ((pair_mem_constantFamilyGraph _ _ _ _).1 indexEntry).2
    have qeq := historySpaces.unique spaceEntry source.1
    have req := historyOrders.unique orderEntry source.2.1
    have veq := historyMeets.unique meetEntry source.2.2
    subst Q R V
    exact births.layerMaps_embedding data group oldAction pairing unions powers separation infinite hG hP0 k mapEntry
  · intro i _ t _ e Q x _ indexEntry mapEntry spaceEntry componentEntry
    obtain rfl := ((pair_mem_constantFamilyGraph _ _ _ _).1 indexEntry).2
    have qeq := historySpaces.unique spaceEntry source.1
    subst Q
    have owned := (pair_mem_graphRestriction.1 componentEntry).1
    have hx := (pair_mem_graphRestriction.1 componentEntry).2
    obtain ⟨_, _, _, _, covered⟩ := births.layerMaps_copy data group oldAction pairing unions powers separation infinite hG hP0 k hx owned mapEntry
    exact covered
  · intro x hx y hy i _ j _ first second different
    exact Or.inl (births.layerComponents_earlier_meet data group oldAction pairing unions powers separation infinite hG hP0 k hx hy first second different)

theorem cutoffLayerSeparatedCode (k n : Nat) (before : k ≤ n) :
    SeparatedLayerCode HQs Hrs Hμs (births.cutoff n) (births.cutoffOrder n)
      (births.cutoffMeet n) (births.cutoffBirth n) (compressionStamp oldTimes k)
      (births.layerOwners k) (births.layerIndices k) (births.layerMaps k)
      (M.groundRelations U B) (births.layerComponents k) (births.layerFiber k) := by
  have full := births.layerSeparatedCode data group oldAction pairing unions powers separation infinite hG hP0
    historySpaces historyOrders historyMeets source k
  refine ⟨full.indices, full.maps, births.layerFiber_cutoff k n before, full.components, ?_, ?_, ?_⟩
  · intro i _ t _ e Q R V indexEntry mapEntry spaceEntry orderEntry meetEntry
    obtain rfl := ((pair_mem_constantFamilyGraph _ _ _ _).1 indexEntry).2
    have qeq := historySpaces.unique spaceEntry source.1
    have req := historyOrders.unique orderEntry source.2.1
    have veq := historyMeets.unique meetEntry source.2.2
    subst Q R V
    exact births.layerMaps_cutoff_embedding data group oldAction pairing unions powers separation infinite hG hP0 k n before mapEntry
  · intro i hi t ht e Q x hx indexEntry mapEntry spaceEntry componentEntry
    obtain ⟨_, u, hu, copied⟩ := (mem_relationImage _ _ _ _).1
      (full.cover i hi t ht e Q x (births.cutoff_subset n hx) indexEntry mapEntry spaceEntry componentEntry)
    exact (mem_relationImage _ _ _ _).2 ⟨hx, u, hu, copied⟩
  · intro x hx y hy i _ j _ first second different
    have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
    obtain ⟨z, a, meetEntry, born, earlier⟩ := births.layerComponents_earlier_meet data group oldAction pairing unions powers separation infinite hG hP0 k hx hy first second different
    have hxCut := ((mem_layerBirthFiber _ _ _ _).1 (births.layerFiber_cutoff k n before ▸ hx)).1
    have hyCut := ((mem_layerBirthFiber _ _ _ _).1 (births.layerFiber_cutoff k n before ▸ hy)).1
    have hz := (ZFSet.pair_mem_prod.1 (geometry.meet.operation.1 meetEntry)).2
    have hzCut := births.cutoff_lower data group oldAction pairing unions powers separation infinite hG hP0 n z hz x hxCut
      (geometry.meet.lower_left x y z meetEntry)
    exact Or.inl ⟨z, a, pair_mem_graphRestriction.2 ⟨meetEntry, ZFSet.pair_mem_prod.2 ⟨hxCut, hyCut⟩⟩,
      pair_mem_graphRestriction.2 ⟨born, hzCut⟩, earlier⟩

theorem layerWitness_spec (k : Nat) {N : ZFSet.{u}} :
    births.layerWitness k ∈ M.sets ∧
      GrowthLayerWitnessCode HQs Hrs Hμs B (completion.externalPointOrder P0 r0 μ0 A0)
        (completion.externalPointMeet P0 r0 μ0 A0) births.birth (compressionStamp oldTimes k) N
        (births.layerWitness k) :=
  ⟨births.layerWitness_ground data group oldAction pairing unions powers separation infinite hG hP0 k,
    Or.inr (Or.inr ⟨_, _, _, _, _, _, rfl,
      births.layerSeparatedCode data group oldAction pairing unions powers separation infinite hG hP0
        historySpaces historyOrders historyMeets source k⟩)⟩

theorem cutoffLayerWitness_spec (k n : Nat) (before : k ≤ n) {N : ZFSet.{u}} :
    births.layerWitness k ∈ M.sets ∧
      GrowthLayerWitnessCode HQs Hrs Hμs (births.cutoff n) (births.cutoffOrder n)
        (births.cutoffMeet n) (births.cutoffBirth n) (compressionStamp oldTimes k) N
        (births.layerWitness k) :=
  ⟨births.layerWitness_ground data group oldAction pairing unions powers separation infinite hG hP0 k,
    Or.inr (Or.inr ⟨_, _, _, _, _, _, rfl,
      births.cutoffLayerSeparatedCode data group oldAction pairing unions powers separation infinite hG hP0
        historySpaces historyOrders historyMeets source k n before⟩)⟩

end PartitionPilot.Forcing.GroundExternalBirthData



namespace PartitionPilot.Forcing.GroundExternalBirthData
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 oldTimes oldBirth : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ P0 r0 μ0 A0 oldTimes oldBirth completion)
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (action : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
variable {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
variable (omega : ZFSet.rank ZFSet.omega < o) (indices : ZFSet.rank I < o)
variable (points : ZFSet.rank P0 < o) (actors : ZFSet.rank G < o)
variable (completed : ZFSet.rank (completion.algebra.union.fields 0) < o)
variable (time : ZFSet.rank oldTimes < o)
include data group action pairing unions powers separation infinite hG hP0
  limit omega indices points actors completed time

theorem layerWitness_rank_lt (k : Nat) : ZFSet.rank (births.layerWitness k) < o := by
  have carrier := completion.externalPointCarrier_rank_lt_of_inputs limit r0 μ0 A0
    omega indices points actors completed
  have vertices := M.externalStarVertices_rank_lt_of_inputs limit r0 μ0 A0 m one
    omega indices points actors
  have fiber := (ZFSet.rank_mono (fun x hx => (births.mem_layerFiber k x).1 hx |>.1)).trans_lt carrier
  have owners := (ZFSet.rank_mono (fun v hv => (births.layerOwners_cases (k := k) hv).1)).trans_lt vertices
  have bound := M.groundRelations_rank_lt limit completed carrier
  exact separatedLayerWitness_rank_lt limit owners
    (rank_constantFamilyGraph_lt limit owners time)
    (rank_functionGraph_lt limit
      (births.layerMaps_spec data group action pairing unions powers separation infinite hG hP0 k).1
      owners bound) bound
    (rank_functionGraph_lt limit
      (births.layerComponents_function data group action pairing unions powers separation infinite hG hP0 k)
      fiber owners) fiber

variable {HQs Hrs Hμs HTime : ZFSet.{u}}
variable (historySpaces : FunctionGraphOn HTime HQs)
variable (historyOrders : FunctionGraphOn HTime Hrs)
variable (historyMeets : FunctionGraphOn HTime Hμs)
variable (source : ZFSet.pair oldTimes (completion.algebra.union.fields 0) ∈ HQs ∧
  ZFSet.pair oldTimes (completion.algebra.union.fields 1) ∈ Hrs ∧
  ZFSet.pair oldTimes (completion.algebra.union.fields 2) ∈ Hμs)
include historySpaces historyOrders historyMeets source

theorem ranked_layerWitness_spec (k : Nat) {N : ZFSet.{u}} :
    births.layerWitness k ∈ M.sets ∧ ZFSet.rank (births.layerWitness k) < o ∧
      GrowthLayerWitnessCode HQs Hrs Hμs (completion.externalPointCarrier P0 r0 μ0 A0)
        (completion.externalPointOrder P0 r0 μ0 A0) (completion.externalPointMeet P0 r0 μ0 A0)
        births.birth (compressionStamp oldTimes k) N (births.layerWitness k) := by
  have code := births.layerWitness_spec data group action pairing unions powers separation infinite hG hP0
    historySpaces historyOrders historyMeets source k (N := N)
  exact ⟨code.1, births.layerWitness_rank_lt data group action pairing unions powers separation infinite
    hG hP0 limit omega indices points actors completed time k, code.2⟩

theorem ranked_cutoffLayerWitness_spec (k n : Nat) (before : k ≤ n) {N : ZFSet.{u}} :
    births.layerWitness k ∈ M.sets ∧ ZFSet.rank (births.layerWitness k) < o ∧
      GrowthLayerWitnessCode HQs Hrs Hμs (births.cutoff n) (births.cutoffOrder n)
        (births.cutoffMeet n) (births.cutoffBirth n) (compressionStamp oldTimes k) N
        (births.layerWitness k) := by
  have code := births.cutoffLayerWitness_spec data group action pairing unions powers separation infinite hG hP0
    historySpaces historyOrders historyMeets source k n before (N := N)
  exact ⟨code.1, births.layerWitness_rank_lt data group action pairing unions powers separation infinite
    hG hP0 limit omega indices points actors completed time k, code.2⟩

end PartitionPilot.Forcing.GroundExternalBirthData

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

end

end PartitionPilot.Forcing

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

namespace PartitionPilot.Forcing.GroundExternalBirthData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 oldTimes oldBirth : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 oldTimes oldBirth completion)
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (action : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
local notation "U" => completion.algebra.union.fields 0
local notation "B" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "E" => completion.externalIdentityCopyGraph P0 r0 μ0 A0
include births data group action pairing unions powers separation infinite hG hP0

theorem ranked_rawPriorWitness {Qs rs μs t N z : ZFSet.{u}}
    (hQs : Qs ∈ M.sets) (hN : N ∈ M.sets) (hz : z ∈ M.sets)
    (code : GrowthLayerWitnessCode Qs rs μs U (completion.algebra.union.fields 1)
      (completion.algebra.union.fields 2) oldBirth t N z)
    (oldTime : t ∈ oldTimes ∨ t = oldTimes) {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (rank : ZFSet.rank z < o) (sourceGraphs : ZFSet.rank Qs < o)
    (target : ZFSet.rank B < o) (numbers : ZFSet.rank N < o) :
    ∃ z' ∈ M.sets, ZFSet.rank z' < o ∧ GrowthLayerWitnessCode Qs rs μs B
      (completion.externalPointOrder P0 r0 μ0 A0) (completion.externalPointMeet P0 r0 μ0 A0)
      births.birth t N z' := by
  have geometry := data.externalGeometryData group action pairing unions powers separation infinite hG hP0
  have embedding := data.externalIdentityCopy_ideal group action pairing unions powers separation infinite hG
  obtain ⟨z', hz', code', rank'⟩ := code.ground_pushforward_rank_lt pairing unions powers separation
    (completion.algebra.union.ground 0) geometry.carrier_ground
    (geometry.copies_ground _ data.group.group_code.identity_mem) hQs hN hz
    limit rank sourceGraphs target numbers completion.algebra.union.meet embedding.toMeetEmbeddingCode
    (fun x y a copied => births.preserves_seed x y a copied)
    (fun _ _ entry => births.priorFiber_image oldTime entry)
  exact ⟨z', hz', rank', code'⟩

theorem ranked_rawCutoffPriorWitness {Qs rs μs t N z : ZFSet.{u}}
    (hQs : Qs ∈ M.sets) (hN : N ∈ M.sets) (hz : z ∈ M.sets)
    (code : GrowthLayerWitnessCode Qs rs μs U (completion.algebra.union.fields 1)
      (completion.algebra.union.fields 2) oldBirth t N z)
    (oldTime : t ∈ oldTimes ∨ t = oldTimes) (n : Nat)
    {o : Ordinal.{u}} (limit : Order.IsSuccLimit o) (rank : ZFSet.rank z < o)
    (sourceGraphs : ZFSet.rank Qs < o) (target : ZFSet.rank B < o) (numbers : ZFSet.rank N < o) :
    ∃ z' ∈ M.sets, ZFSet.rank z' < o ∧ GrowthLayerWitnessCode Qs rs μs (births.cutoff n)
      (births.cutoffOrder n) (births.cutoffMeet n) (births.cutoffBirth n) t N z' := by
  have geometry := data.externalGeometryData group action pairing unions powers separation infinite hG hP0
  have embedding := data.externalIdentityCopy_ideal group action pairing unions powers separation infinite hG
  have contained : ∀ x y, ZFSet.pair x y ∈ E → y ∈ births.cutoff n := by
    intro x y copied
    have bounds := ZFSet.pair_mem_prod.1 (embedding.injection.function.1 copied)
    exact births.cutoff_old n ((mem_relationImage U B E y).2 ⟨bounds.2, x, bounds.1, copied⟩)
  have restricted := embedding.toMeetEmbeddingCode.restrictTarget (Q := births.cutoff n) contained
  have family := births.cutoffFamily_spec data group action pairing unions powers separation infinite hG hP0
  have hCut := M.pair_right (M.transitive family.1 ((family.2.2 n _).2 rfl))
  have preserves : ∀ x y a, ZFSet.pair x y ∈ E →
      (ZFSet.pair y a ∈ births.cutoffBirth n ↔ ZFSet.pair x a ∈ oldBirth) := by
    intro x y a copied
    change ZFSet.pair y a ∈ graphRestriction (births.cutoff n) births.birth ↔ _
    rw [pair_mem_graphRestriction]
    exact (and_iff_left (contained x y copied)).trans (births.preserves_seed x y a copied)
  obtain ⟨z', hz', code', rank'⟩ := code.ground_pushforward_rank_lt pairing unions powers separation
    (completion.algebra.union.ground 0) hCut
    (geometry.copies_ground _ data.group.group_code.identity_mem) hQs hN hz
    limit rank sourceGraphs ((ZFSet.rank_mono (births.cutoff_subset n)).trans_lt target) numbers
    completion.algebra.union.meet restricted preserves
    (fun _ _ entry => births.priorFiber_image oldTime (pair_mem_graphRestriction.1 entry).1)
  exact ⟨z', hz', rank', code'⟩

end PartitionPilot.Forcing.GroundExternalBirthData

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundExternalSerializedCore
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroundExternalBirthData
open SetFormula
open scoped ZFSet
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 oldTimes oldBirth C D rD lo hi seed T0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 oldTimes oldBirth completion)
variable (heights : GroundExternalHeightData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 C D rD lo hi seed completion)
variable (prior : GroundSerializedChronology M T0 C D rD)
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (action : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
variable (hOld : oldTimes ∈ T0)

local notation "fields" => births.serializedFields heights prior data group action
  pairing unions powers separation infinite hG hP0 hOld

include births heights prior data group action pairing unions powers separation infinite hG hP0 hOld

theorem serializedFields_value (j : Fin 5) {s : ZFSet.{u}}
    (hs : s ∈ insert births.limit births.limit) :
    (fields).value j s = (births.chronologyFields heights prior.toHistory).fieldValue j s := by
  apply births.groundChronologyFields_values heights prior.fields data group action
    pairing unions powers separation infinite hG hP0 prior.ordinal hOld prior.toHistory ?_ j hs
  intro k a _
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))) k

theorem serializedFields_core :
    ChronologyCoreCode (insert births.limit births.limit) (fields).bound C D rD (fields).graph := by
  refine ⟨(fields).function, ?_⟩
  intro s hs L r μ birth height eL er eμ eb eh
  have v (j : Fin 5) := births.serializedFields_value heights prior data group action
    pairing unions powers separation infinite hG hP0 hOld j hs
  have laws := births.chronologyFields_stage_laws heights prior.toHistory data group action
    pairing unions powers separation infinite hG hP0 prior.ordinal hOld hs
  rw [← (fields).value_eq_of_entry 0 eL, ← (fields).value_eq_of_entry 1 er,
    ← (fields).value_eq_of_entry 2 eμ, ← (fields).value_eq_of_entry 3 eb,
    ← (fields).value_eq_of_entry 4 eh, v 0, v 1, v 2, v 3, v 4]
  exact ⟨laws.1, laws.2.1, laws.2.2.1, laws.2.2.2.1, laws.2.2.2.2⟩

theorem serializedFields_old (j : Fin 5) {s : ZFSet.{u}}
    (before : s ∈ oldTimes ∨ s = oldTimes) :
    (fields).value j s = prior.fields.value j s := by
  have hs : s ∈ insert births.limit births.limit := ZFSet.mem_insert_of_mem _
    ((births.times.mem_limit_iff s).2 (before.elim Or.inl (fun h => Or.inr (Or.inl h))))
  rw [births.serializedFields_value heights prior data group action
    pairing unions powers separation infinite hG hP0 hOld j hs]
  have values := births.chronologyFields_old heights prior.toHistory before
  exact Fin.cases values.1 (Fin.cases values.2.1 (Fin.cases values.2.2.1
    (Fin.cases values.2.2.2.1 (Fin.cases values.2.2.2.2 (fun i => Fin.elim0 i))))) j

theorem serializedFields_stamp (j : Fin 5) (n : Nat) :
    (fields).value j (compressionStamp oldTimes n) = births.cutoffField heights j n := by
  rw [births.serializedFields_value heights prior data group action
    pairing unions powers separation infinite hG hP0 hOld j
      (ZFSet.mem_insert_of_mem _ (births.times.stamp_mem_limit n))]
  have values := births.chronologyFields_stamp heights prior.toHistory n
  exact Fin.cases values.1 (Fin.cases values.2.1 (Fin.cases values.2.2.1
    (Fin.cases values.2.2.2.1 (Fin.cases values.2.2.2.2 (fun i => Fin.elim0 i))))) j

theorem serializedFields_limit (j : Fin 5) :
    (fields).value j births.limit = births.terminalField heights j := by
  rw [births.serializedFields_value heights prior data group action
    pairing unions powers separation infinite hG hP0 hOld j (ZFSet.mem_insert _ _)]
  have values := births.chronologyFields_limit heights prior.toHistory
  exact Fin.cases values.1 (Fin.cases values.2.1 (Fin.cases values.2.2.1
    (Fin.cases values.2.2.2.1 (Fin.cases values.2.2.2.2 (fun i => Fin.elim0 i))))) j

theorem serializedFields_old_entries (j : Fin 5) {s : ZFSet.{u}}
    (before : s ∈ oldTimes ∨ s = oldTimes) (y : ZFSet.{u}) :
    ZFSet.pair s y ∈ (fields).graph j ↔ ZFSet.pair s y ∈ prior.fields.graph j := by
  have oldValue := births.serializedFields_old heights prior data group action
    pairing unions powers separation infinite hG hP0 hOld j before
  have hs : s ∈ T0 := before.elim (fun h => prior.ordinal.1 oldTimes hOld s h) (fun h => h.symm ▸ hOld)
  have hs' : s ∈ insert births.limit births.limit := ZFSet.mem_insert_of_mem _
    ((births.times.mem_limit_iff s).2 (before.elim Or.inl (fun h => Or.inr (Or.inl h))))
  constructor
  · intro entry
    have equal := oldValue.symm.trans ((fields).value_eq_of_entry j entry)
    exact equal ▸ prior.fields.value_entry j hs
  · intro entry
    have equal := oldValue.trans (prior.fields.value_eq_of_entry j entry)
    exact equal ▸ (fields).value_entry j hs'

end PartitionPilot.Forcing.GroundExternalBirthData

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundExternalSerializedChronology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.GroundExternalBirthData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 oldTimes oldBirth C D rD lo hi seed T0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 oldTimes oldBirth completion)
variable (heights : GroundExternalHeightData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 C D rD lo hi seed completion)
variable (prior : GroundSerializedChronology M T0 C D rD)
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (action : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
variable (hOld : oldTimes ∈ T0)

local notation "fields" => births.serializedFields heights prior data group action
  pairing unions powers separation infinite hG hP0 hOld
local notation "U" => completion.algebra.union.fields 0
include births heights prior data group action pairing unions powers separation infinite hG hP0 hOld

variable (source : prior.fields.value 0 oldTimes = completion.algebra.union.fields 0 ∧
  prior.fields.value 1 oldTimes = completion.algebra.union.fields 1 ∧
  prior.fields.value 2 oldTimes = completion.algebra.union.fields 2 ∧
  prior.fields.value 3 oldTimes = oldBirth)
include source

theorem serialized_base_entries :
    ZFSet.pair oldTimes U ∈ (fields).graph 0 ∧
      ZFSet.pair oldTimes (completion.algebra.union.fields 1) ∈ (fields).graph 1 ∧
      ZFSet.pair oldTimes (completion.algebra.union.fields 2) ∈ (fields).graph 2 := by
  have hs := ZFSet.mem_insert_of_mem births.limit births.times.base_mem_limit
  have values (j : Fin 5) := births.serializedFields_old heights prior data group action
    pairing unions powers separation infinite hG hP0 hOld j (Or.inr rfl)
  exact ⟨(values 0 |>.trans source.1) ▸ (fields).value_entry 0 hs,
    (values 1 |>.trans source.2.1) ▸ (fields).value_entry 1 hs,
    (values 2 |>.trans source.2.2.1) ▸ (fields).value_entry 2 hs⟩

end PartitionPilot.Forcing.GroundExternalBirthData




namespace PartitionPilot.Forcing.GroundExternalBirthData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 oldTimes oldBirth C D rD lo hi seed T0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 oldTimes oldBirth completion)
variable (heights : GroundExternalHeightData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 C D rD lo hi seed completion)
variable (prior : GroundSerializedChronology M T0 C D rD)
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (action : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
variable (hOld : oldTimes ∈ T0)
local notation "fields" => births.serializedFields heights prior data group action
  pairing unions powers separation infinite hG hP0 hOld
local notation "U" => completion.algebra.union.fields 0
local notation "B" => completion.externalPointCarrier P0 r0 μ0 A0
include births heights prior data group action pairing unions powers separation infinite hG hP0 hOld

theorem ranked_prior_source_entries {t : ZFSet.{u}}
    (oldTime : t ∈ oldTimes ∨ t = oldTimes) (j : Fin 5) :
    ∀ a ∈ t, ∀ y, ZFSet.pair a y ∈ prior.fields.graph j ↔ ZFSet.pair a y ∈ (fields).graph j := by
  intro a ha y
  have baseOrdinal := ordinalSetProperty_member births.times.ordinal births.times.base_mem_limit
  have earlier : a ∈ oldTimes := oldTime.elim
    (fun member => baseOrdinal.1 t member a ha) (fun equal => equal ▸ ha)
  exact (births.serializedFields_old_entries heights prior data group action
    pairing unions powers separation infinite hG hP0 hOld j (Or.inl earlier) y).symm

variable {o : Ordinal.{u}} (priorRank : ZFSet.rank prior.code < o)
include priorRank

theorem serialized_old_ranked_raw_witness {s t : ZFSet.{u}}
    (before : s ∈ oldTimes ∨ s = oldTimes) (earlier : t = s ∨ t ∈ s) :
    ∃ z ∈ M.sets, ZFSet.rank z < o ∧
      GrowthLayerWitnessCode ((fields).graph 0) ((fields).graph 1) ((fields).graph 2)
        ((fields).value 0 s) ((fields).value 1 s) ((fields).value 2 s) ((fields).value 3 s) t ZFSet.omega z := by
  have baseOrdinal := ordinalSetProperty_member births.times.ordinal births.times.base_mem_limit
  have hs : s ∈ T0 := before.elim (fun h => prior.ordinal.1 oldTimes hOld s h) (fun h => h.symm ▸ hOld)
  have ht : t ∈ T0 := earlier.elim (fun h => h.symm ▸ hs) (fun h => prior.ordinal.1 s hs t h)
  have oldTime : t ∈ oldTimes ∨ t = oldTimes := by
    rcases earlier with rfl | h
    · exact before
    · exact Or.inl (before.elim (fun member => baseOrdinal.1 s member t h) (fun equal => equal ▸ h))
  have agree (j : Fin 5) := births.ranked_prior_source_entries heights prior data group action
    pairing unions powers separation infinite hG hP0 hOld oldTime j
  have code := (prior.layer_code s hs t ht earlier _ (prior.layerWitness_entry hs ht earlier)).congr_source_entries
    (agree 0) (agree 1) (agree 2)
  refine ⟨prior.layerWitness s t, prior.layerWitness_ground s t,
    (prior.layerWitness_rank_lt_code hs ht earlier).trans priorRank, ?_⟩
  rw [births.serializedFields_old heights prior data group action pairing unions powers separation infinite hG hP0 hOld 0 before,
    births.serializedFields_old heights prior data group action pairing unions powers separation infinite hG hP0 hOld 1 before,
    births.serializedFields_old heights prior data group action pairing unions powers separation infinite hG hP0 hOld 2 before,
    births.serializedFields_old heights prior data group action pairing unions powers separation infinite hG hP0 hOld 3 before]
  exact code

variable (source : prior.fields.value 0 oldTimes = completion.algebra.union.fields 0 ∧
  prior.fields.value 1 oldTimes = completion.algebra.union.fields 1 ∧
  prior.fields.value 2 oldTimes = completion.algebra.union.fields 2 ∧
  prior.fields.value 3 oldTimes = oldBirth)
include source

omit births heights data group action pairing unions powers separation infinite hG hP0 in
theorem serialized_terminal_prior_ranked_witness (t : ZFSet.{u})
    (oldTime : t ∈ oldTimes ∨ t = oldTimes) :
    ∃ z ∈ M.sets, ZFSet.rank z < o ∧
      GrowthLayerWitnessCode (prior.fields.graph 0) (prior.fields.graph 1) (prior.fields.graph 2)
        U (completion.algebra.union.fields 1) (completion.algebra.union.fields 2) oldBirth t ZFSet.omega z := by
  have ht : t ∈ T0 := oldTime.elim
    (fun h => prior.ordinal.1 oldTimes hOld t h) (fun h => h.symm ▸ hOld)
  have code := prior.layer_code oldTimes hOld t ht oldTime.symm _
    (prior.layerWitness_entry hOld ht oldTime.symm)
  refine ⟨prior.layerWitness oldTimes t, prior.layerWitness_ground oldTimes t,
    (prior.layerWitness_rank_lt_code hOld ht oldTime.symm).trans priorRank, ?_⟩
  simpa only [source.1, source.2.1, source.2.2.1, source.2.2.2] using code

theorem serialized_all_ranked_raw_witnesses (limit : Order.IsSuccLimit o)
    (omega : ZFSet.rank ZFSet.omega < o) (indices : ZFSet.rank I < o)
    (points : ZFSet.rank P0 < o) (actors : ZFSet.rank G < o) :
    ∀ s ∈ insert births.limit births.limit, ∀ t ∈ insert births.limit births.limit,
      t = s ∨ t ∈ s → ∃ z ∈ M.sets, ZFSet.rank z < o ∧
        GrowthLayerWitnessCode ((fields).graph 0) ((fields).graph 1) ((fields).graph 2)
          ((fields).value 0 s) ((fields).value 1 s) ((fields).value 2 s) ((fields).value 3 s) t ZFSet.omega z := by
  have completed : ZFSet.rank U < o := by
    rw [← source.1]
    exact (prior.fieldValue_rank_lt_code 0 hOld).trans priorRank
  have time : ZFSet.rank oldTimes < o :=
    ((ZFSet.rank_lt_of_mem hOld).trans_le prior.time_rank_le_code).trans priorRank
  have carrier := completion.externalPointCarrier_rank_lt_of_inputs limit r0 μ0 A0
    omega indices points actors completed
  have sources := births.serialized_base_entries heights prior data group action
    pairing unions powers separation infinite hG hP0 hOld source
  have old (s t : ZFSet.{u}) (before : s ∈ oldTimes ∨ s = oldTimes) (earlier : t = s ∨ t ∈ s) :=
    births.serialized_old_ranked_raw_witness heights prior data group action
      pairing unions powers separation infinite hG hP0 hOld priorRank before earlier
  have base (t : ZFSet.{u}) (oldTime : t ∈ oldTimes ∨ t = oldTimes) :=
    serialized_terminal_prior_ranked_witness prior hOld priorRank source t oldTime
  have finite (n : Nat) (t : ZFSet.{u}) (bound : t = compressionStamp oldTimes n ∨ t ∈ compressionStamp oldTimes n) :
      ∃ z ∈ M.sets, ZFSet.rank z < o ∧ GrowthLayerWitnessCode
        ((fields).graph 0) ((fields).graph 1) ((fields).graph 2)
        ((fields).value 0 (compressionStamp oldTimes n)) ((fields).value 1 (compressionStamp oldTimes n))
        ((fields).value 2 (compressionStamp oldTimes n)) ((fields).value 3 (compressionStamp oldTimes n)) t ZFSet.omega z := by
    rw [births.serializedFields_stamp heights prior data group action pairing unions powers separation infinite hG hP0 hOld 0 n,
      births.serializedFields_stamp heights prior data group action pairing unions powers separation infinite hG hP0 hOld 1 n,
      births.serializedFields_stamp heights prior data group action pairing unions powers separation infinite hG hP0 hOld 2 n,
      births.serializedFields_stamp heights prior data group action pairing unions powers separation infinite hG hP0 hOld 3 n]
    change ∃ z ∈ M.sets, ZFSet.rank z < o ∧ GrowthLayerWitnessCode _ _ _ (births.cutoff n)
      (births.cutoffOrder n) (births.cutoffMeet n) (births.cutoffBirth n) t ZFSet.omega z
    have fresh (k : Nat) (before : k ≤ n) := births.ranked_cutoffLayerWitness_spec data group action
      pairing unions powers separation infinite hG hP0 limit omega indices points actors completed time
      ⟨_, (fields).function 0⟩ ⟨_, (fields).function 1⟩ ⟨_, (fields).function 2⟩ sources k n before (N := ZFSet.omega)
    have original (a : ZFSet.{u}) (oldTime : a ∈ oldTimes ∨ a = oldTimes) :
        ∃ z ∈ M.sets, ZFSet.rank z < o ∧ GrowthLayerWitnessCode ((fields).graph 0) ((fields).graph 1) ((fields).graph 2)
          (births.cutoff n) (births.cutoffOrder n) (births.cutoffMeet n) (births.cutoffBirth n) a ZFSet.omega z := by
      obtain ⟨z, hz, rank, code⟩ := base a oldTime
      obtain ⟨z', hz', rank', code'⟩ := births.ranked_rawCutoffPriorWitness data group action
        pairing unions powers separation infinite hG hP0 (prior.fields.graph_ground 0)
        (M.omega_mem separation infinite) hz code oldTime n limit rank
        ((prior.fieldGraph_rank_le_code 0).trans_lt priorRank) carrier omega
      have agree (j : Fin 5) := births.ranked_prior_source_entries heights prior data group action
        pairing unions powers separation infinite hG hP0 hOld oldTime j
      exact ⟨z', hz', rank', code'.congr_source_entries (agree 0) (agree 1) (agree 2)⟩
    rcases bound with rfl | before
    · exact ⟨_, fresh n (Nat.le_refl n)⟩
    · rcases (mem_compressionStamp_iff oldTimes t n).1 before with h | h | ⟨k, earlier, rfl⟩
      · exact original t (Or.inl h)
      · exact original t (Or.inr h)
      · exact ⟨_, fresh k (Nat.le_of_lt earlier)⟩
  have terminal (t : ZFSet.{u}) (bound : t = births.limit ∨ t ∈ births.limit) :
      ∃ z ∈ M.sets, ZFSet.rank z < o ∧ GrowthLayerWitnessCode
        ((fields).graph 0) ((fields).graph 1) ((fields).graph 2)
        ((fields).value 0 births.limit) ((fields).value 1 births.limit)
        ((fields).value 2 births.limit) ((fields).value 3 births.limit) t ZFSet.omega z := by
    rw [births.serializedFields_limit heights prior data group action pairing unions powers separation infinite hG hP0 hOld 0,
      births.serializedFields_limit heights prior data group action pairing unions powers separation infinite hG hP0 hOld 1,
      births.serializedFields_limit heights prior data group action pairing unions powers separation infinite hG hP0 hOld 2,
      births.serializedFields_limit heights prior data group action pairing unions powers separation infinite hG hP0 hOld 3]
    change ∃ z ∈ M.sets, ZFSet.rank z < o ∧ GrowthLayerWitnessCode _ _ _ B
      (completion.externalPointOrder P0 r0 μ0 A0) (completion.externalPointMeet P0 r0 μ0 A0) births.birth t ZFSet.omega z
    have fresh (k : Nat) := births.ranked_layerWitness_spec data group action
      pairing unions powers separation infinite hG hP0 limit omega indices points actors completed time
      ⟨_, (fields).function 0⟩ ⟨_, (fields).function 1⟩ ⟨_, (fields).function 2⟩ sources k (N := ZFSet.omega)
    have original (a : ZFSet.{u}) (oldTime : a ∈ oldTimes ∨ a = oldTimes) :
        ∃ z ∈ M.sets, ZFSet.rank z < o ∧ GrowthLayerWitnessCode ((fields).graph 0) ((fields).graph 1) ((fields).graph 2)
          B (completion.externalPointOrder P0 r0 μ0 A0) (completion.externalPointMeet P0 r0 μ0 A0) births.birth a ZFSet.omega z := by
      obtain ⟨z, hz, rank, code⟩ := base a oldTime
      obtain ⟨z', hz', rank', code'⟩ := births.ranked_rawPriorWitness data group action
        pairing unions powers separation infinite hG hP0 (prior.fields.graph_ground 0)
        (M.omega_mem separation infinite) hz code oldTime limit rank
        ((prior.fieldGraph_rank_le_code 0).trans_lt priorRank) carrier omega
      have agree (j : Fin 5) := births.ranked_prior_source_entries heights prior data group action
        pairing unions powers separation infinite hG hP0 hOld oldTime j
      exact ⟨z', hz', rank', code'.congr_source_entries (agree 0) (agree 1) (agree 2)⟩
    rcases bound with rfl | before
    · have hEmpty := M.empty_mem ⟨births.limit, births.limit_ground⟩
      have emptyRank : ZFSet.rank (∅ : ZFSet.{u}) < o := by simpa only [ZFSet.rank_empty] using limit.pos
      refine ⟨countableLayerWitness ∅ ∅, M.countableLayerWitness_mem pairing hEmpty hEmpty,
        countableLayerWitness_rank_lt limit emptyRank emptyRank,
        Or.inl ⟨∅, ∅, rfl, ⟨InjectionCode.empty ZFSet.omega, ?_⟩⟩⟩
      intro x _ born
      exact (births.no_limit_birth x born).elim
    · rcases (births.times.mem_limit_iff t).1 before with h | h | ⟨k, rfl⟩
      · exact original t (Or.inl h)
      · exact original t (Or.inr h)
      · exact ⟨_, fresh k⟩
  intro s hs t _ bound
  rcases ZFSet.mem_insert_iff.1 hs with rfl | before
  · exact terminal t bound
  · rcases (births.times.mem_limit_iff s).1 before with h | h | ⟨n, rfl⟩
    · exact old s t (Or.inl h) bound
    · exact old s t (Or.inr h) bound
    · exact finite n t bound

end PartitionPilot.Forcing.GroundExternalBirthData



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



namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem GroundChronologicalHistory.fieldValue_eq_of_heq
    {M : TransitiveGround.{u}} {T T' C D rD : ZFSet.{u}}
    {first : GroundChronologicalHistory M T C D rD}
    {second : GroundChronologicalHistory M T' C D rD}
    (times : T = T') (same : HEq first second) (j : Fin 5) (s : ZFSet.{u}) :
    first.fieldValue j s = second.fieldValue j s := by
  cases times
  cases eq_of_heq same
  rfl

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundInitialMainSuccessorData
universe u
variable {M : TransitiveGround.{u}} {C D rD Labels : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)
local notation "comp" => certificate.compression
local notation "completion" => certificate.compression.born.profiled.heighted.completion
local notation "births" => certificate.births
local notation "external" => certificate.external
variable {o : Ordinal.{u}}
variable (completed : ZFSet.rank (certificate.compression.born.profiled.heighted.completion.algebra.union.fields 0) < o)
variable (prior : ∀ s ∈ insert source.cutoff source.cutoff, ZFSet.rank (source.history.space s) < o)
include completed prior

theorem compression_history_carrier_rank_lt {s : ZFSet.{u}}
    (hs : s ∈ insert (comp).born.births.limit (comp).born.births.limit) :
    ZFSet.rank ((comp).history.space s) < o := by
  rcases ZFSet.mem_insert_iff.1 hs with rfl | hs
  · rw [(comp).limit_values.1]
    exact completed
  · rcases ((comp).born.births.times.mem_limit_iff s).1 hs with before | equal | ⟨n, rfl⟩
    · rw [((comp).old_values s (Or.inl before)).1]
      exact prior s (ZFSet.mem_insert_of_mem _ before)
    · rw [((comp).old_values s (Or.inr equal)).1]
      exact prior s (equal.symm ▸ ZFSet.mem_insert _ _)
    · rw [((comp).stamp_values n).1]
      exact (ZFSet.rank_mono (((completion).algebra.union.fieldUnion 0).subset (n + 1))).trans_lt completed

theorem external_history_carrier_rank_lt
    (points : ZFSet.rank ((completion).externalPointCarrier source.stage.carrier
      source.stage.order source.stage.meetGraph source.stage.action) < o)
    {s : ZFSet.{u}} (hs : s ∈ insert (births).limit (births).limit) :
    ZFSet.rank ((external).history.space s) < o := by
  rcases ZFSet.mem_insert_iff.1 hs with rfl | hs
  · rw [(external).limit_values.1]
    exact points
  · rcases ((births).times.mem_limit_iff s).1 hs with before | equal | ⟨n, rfl⟩
    · rw [((external).old_values s (Or.inl before)).1]
      exact certificate.compression_history_carrier_rank_lt completed prior (ZFSet.mem_insert_of_mem _ before)
    · rw [((external).old_values s (Or.inr equal)).1]
      exact certificate.compression_history_carrier_rank_lt completed prior (equal.symm ▸ ZFSet.mem_insert _ _)
    · rw [((external).stamp_values n).1]
      exact (ZFSet.rank_mono ((births).cutoff_subset n)).trans_lt points

end PartitionPilot.Forcing.GroundInitialMainSuccessorData



namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem GroundSerializedChronology.agreeing_history_carrier_rank_lt
    {M : TransitiveGround.{u}} {T C D rD : ZFSet.{u}}
    (serial : GroundSerializedChronology M T C D rD)
    (history : GroundChronologicalHistory M T C D rD)
    {o : Ordinal.{u}} (rank : ZFSet.rank serial.code < o)
    (agreement : ∀ j s, s ∈ T → serial.fields.value j s = history.fieldValue j s)
    {s : ZFSet.{u}} (hs : s ∈ T) : ZFSet.rank (history.space s) < o := by
  have bound := (serial.fieldValue_rank_lt_code 0 hs).trans rank
  rw [agreement 0 s hs] at bound
  exact bound

namespace GroundInitialMainSuccessorData
variable {M : TransitiveGround.{u}} {C D rD Labels K : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
variable (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
variable (invariant : source.Invariant K Labels)
variable (prior : GroundSerializedChronology M (insert source.cutoff source.cutoff) C D rD)
variable (priorRank : ZFSet.rank prior.code < ZFSet.rank K)
variable (priorAgreement : ∀ j s, s ∈ insert source.cutoff source.cutoff →
  prior.fields.value j s = source.history.fieldValue j s)
include certificate pairing unions powers separation collection infinite hK conditions invariant priorRank priorAgreement
local notation "comp" => certificate.compression
local notation "births" => certificate.births
local notation "external" => certificate.external

theorem compressionFieldGraphs_rank_lt
    (fields : GroundChronologyFields M (insert (comp).born.births.limit (comp).born.births.limit))
    (agreement : ∀ j s, s ∈ insert (comp).born.births.limit (comp).born.births.limit →
      fields.value j s = (comp).history.fieldValue j s) (j : Fin 5) :
    ZFSet.rank (fields.graph j) < ZFSet.rank K := by
  have completed := certificate.compression_union_rank_lt pairing unions powers separation collection infinite
    hK conditions invariant.points_rank invariant.labels_rank
  have times := conditions.successor_mem pairing unions powers separation infinite hK
    (certificate.compression_limit_mem pairing unions powers separation infinite hK conditions invariant.cutoff_mem)
  exact fields.graph_rank_lt_of_history pairing unions powers separation collection infinite hK conditions times
    (comp).history agreement
    (fun _ hs => certificate.compression_history_carrier_rank_lt completed
      (fun _ ht => prior.agreeing_history_carrier_rank_lt source.history priorRank priorAgreement ht) hs)
    invariant.columns_rank invariant.coordinates_rank j

theorem externalFieldGraphs_rank_lt
    (fields : GroundChronologyFields M (insert (births).limit (births).limit))
    (agreement : ∀ j s, s ∈ insert (births).limit (births).limit →
      fields.value j s = (external).history.fieldValue j s) (j : Fin 5) :
    ZFSet.rank (fields.graph j) < ZFSet.rank K := by
  have completed := certificate.compression_union_rank_lt pairing unions powers separation collection infinite
    hK conditions invariant.points_rank invariant.labels_rank
  have target := (certificate.target_rank_lt pairing unions powers separation collection infinite
    hK conditions invariant.points_rank invariant.labels_rank invariant.actors_rank).1
  rw [certificate.target_fields.1] at target
  have points := (ZFSet.rank_mono (fixedTopCarrier_subset _)).trans_lt target
  have times := conditions.successor_mem pairing unions powers separation infinite hK
    (certificate.external_limit_mem pairing unions powers separation infinite hK conditions invariant.cutoff_mem)
  exact fields.graph_rank_lt_of_history pairing unions powers separation collection infinite hK conditions times
    (external).history agreement
    (fun _ hs => certificate.external_history_carrier_rank_lt completed
      (fun _ ht => prior.agreeing_history_carrier_rank_lt source.history priorRank priorAgreement ht) points hs)
    invariant.columns_rank invariant.coordinates_rank j

end GroundInitialMainSuccessorData

end PartitionPilot.Forcing




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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundRankedBoundedSerialization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroundInitialMainSuccessorData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD Labels K : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
variable (invariant : source.Invariant K Labels) (level : GroundMainCandidateLevel M K)
local notation "births" => certificate.births
local notation "heights" => certificate.heights
local notation "external" => certificate.external
include pairing unions powers separation collection infinite choice hK conditions invariant

theorem exists_rankedBoundedSerialization
    (prior : GroundSerializedChronology M (insert (births).limit (births).limit) C D rD)
    (priorRank : ZFSet.rank prior.code < ZFSet.rank K)
    (agreement : ∀ j s, s ∈ insert (births).limit (births).limit →
      prior.fields.value j s = (external).history.fieldValue j s) :
    ∃ serial : GroundSerializedChronology M (insert (births).limit (births).limit) C D rD,
      serial.code ∈ M.sets ∧ ZFSet.rank serial.code < ZFSet.rank K ∧
        serial.code ∈ level.validChronologies C D rD ∧ ∀ j s, s ∈ insert (births).limit (births).limit →
        serial.fields.value j s = (external).bounded_history.fieldValue j s := by
  have space := (agreement 0 (births).limit (ZFSet.mem_insert _ _)).trans (external).limit_values.1
  have order := (agreement 1 (births).limit (ZFSet.mem_insert _ _)).trans (external).limit_values.2.1
  have birth := (agreement 3 (births).limit (ZFSet.mem_insert _ _)).trans (external).limit_values.2.2.2.1
  have earlier : ∀ x t, ZFSet.pair x t ∈ prior.fields.value 3 (births).limit → t ∈ (births).limit := by
    intro x t entry
    rw [birth] at entry
    exact (ZFSet.pair_mem_prod.1 ((births).function.1 entry)).2
  have heightCode : StrictLexHeightCode (fixedTopCarrier (prior.fields.value 0 (births).limit)) C D
      (fixedTopOrder (prior.fields.value 0 (births).limit) (prior.fields.value 1 (births).limit))
      (heights).boundedHeight rD := by
    rw [space, order]
    exact certificate.boundedHeights.code
  have limit := conditions.rank_isLimit pairing unions powers separation infinite hK
  have time := conditions.successor_mem pairing unions powers separation infinite hK
    (certificate.external_limit_mem pairing unions powers separation infinite hK conditions invariant.cutoff_mem)
  have points := (certificate.target_rank_lt pairing unions powers separation collection infinite
    hK conditions invariant.points_rank invariant.labels_rank invariant.actors_rank).1
  rw [certificate.target_fields.1] at points
  have heightRank := SetRealization.rank_functionGraph_lt limit certificate.boundedHeights.code.function
    points (SetRealization.rank_product_lt limit invariant.columns_rank invariant.coordinates_rank)
  obtain ⟨serial, ground, rank, member, _, values⟩ := prior.exists_rankedFixedTopSerialization
    pairing unions powers separation collection infinite choice hK conditions time level priorRank
    (heights).boundedHeight certificate.boundedHeights.height_ground heightRank
    (births).times.ordinal earlier heightCode
  have terminal (j : Fin 5) : prior.fixedTopValues (heights).boundedHeight j =
      (external).bounded_history.fieldValue j (births).limit := by
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))) j
    · change fixedTopCarrier (prior.fields.value 0 (births).limit) = _
      rw [space]
      exact (external).bounded_values.1.symm
    · change fixedTopOrder (prior.fields.value 0 (births).limit) (prior.fields.value 1 (births).limit) = _
      rw [space, order]
      exact (external).bounded_values.2.1.symm
    · change fixedTopMeet (prior.fields.value 0 (births).limit) (prior.fields.value 1 (births).limit) = _
      rw [space, order]
      exact (external).bounded_values.2.2.1.symm
    · change fixedTopBirth (prior.fields.value 0 (births).limit) (prior.fields.value 3 (births).limit) (births).limit = _
      rw [space, birth]
      exact (external).bounded_values.2.2.2.1.symm
    · exact (external).bounded_values.2.2.2.2.symm
  refine ⟨serial, ground, rank, member, ?_⟩
  intro j s hs
  rw [values j s hs]
  rcases ZFSet.mem_insert_iff.1 hs with rfl | hs
  · rw [appendHistoryValue_at]
    exact terminal j
  · rw [appendHistoryValue_old hs]
    have previous := (external).bounded_old_values s hs
    have same : (external).bounded_history.fieldValue j s = (external).history.fieldValue j s :=
      Fin.cases previous.1 (Fin.cases previous.2.1 (Fin.cases previous.2.2.1
        (Fin.cases previous.2.2.2.1 (Fin.cases previous.2.2.2.2 (fun i => Fin.elim0 i))))) j
    exact (agreement j s (ZFSet.mem_insert_of_mem _ hs)).trans same.symm

end PartitionPilot.Forcing.GroundInitialMainSuccessorData

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundRankedCompressionSerialization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.GroundInitialMainSuccessorData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD Labels K : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)
local notation "comp" => certificate.compression

theorem exists_rankedCompressionSerialization
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    (invariant : source.Invariant K Labels) (level : GroundMainCandidateLevel M K)
    (prior : GroundSerializedChronology M (insert source.cutoff source.cutoff) C D rD)
    (priorRank : ZFSet.rank prior.code < ZFSet.rank K)
    (agreement : ∀ j s, s ∈ insert source.cutoff source.cutoff →
      prior.fields.value j s = source.history.fieldValue j s) :
    ∃ serial : GroundSerializedChronology M (insert (comp).born.births.limit (comp).born.births.limit) C D rD,
      serial.code ∈ M.sets ∧ ZFSet.rank serial.code < ZFSet.rank K ∧
      serial.code ∈ level.validChronologies C D rD ∧
      (∀ j s, s ∈ insert (comp).born.births.limit (comp).born.births.limit →
        serial.fields.value j s = (comp).history.fieldValue j s) ∧
      serial.layerBound = functionGraphRange
        (chronologyPairs (insert (comp).born.births.limit (comp).born.births.limit)) serial.layers := by
  have limit := conditions.rank_isLimit pairing unions powers separation infinite hK
  have tasks : ZFSet.rank (source.stage.compressionTasks Labels) < ZFSet.rank K :=
    M.groundEligibleTasks_rank_lt limit source.stage.actors source.stage.order
      source.stage.meetGraph source.stage.action invariant.points_rank invariant.labels_rank
  obtain ⟨fields, _, core, values, raw⟩ := certificate.origin.exists_rankedRawCompressionFields comp prior
    pairing unions powers separation collection infinite
    certificate.indices_ground certificate.sources_ground certificate.representatives_ground
    source.stage.actors_ground certificate.task_action_ground (ZFSet.mem_insert _ _)
    limit priorRank tasks tasks
    (M.initialCompressionData_template_constancy source.stage.carrier source.stage.actors
      source.stage.order source.stage.meetGraph source.stage.action Labels)
    rfl rfl rfl source.carrier_eq source.order_eq source.meet_eq rfl agreement
  have graphs := certificate.compressionFieldGraphs_rank_lt pairing unions powers separation
    collection infinite hK conditions invariant prior priorRank agreement fields values
  have times := conditions.successor_mem pairing unions powers separation infinite hK
    (certificate.compression_limit_mem pairing unions powers separation infinite hK conditions invariant.cutoff_mem)
  obtain ⟨serial, ground, rank, member, _, exactValues, exactRange⟩ :=
    fields.exists_rankedSerialization pairing unions powers separation collection infinite choice
      hK conditions times level (ordinalSetProperty_succ (comp).born.births.times.ordinal) core graphs raw
  exact ⟨serial, ground, rank, member, fun j s hs => (exactValues j s).trans (values j s hs), exactRange⟩

end PartitionPilot.Forcing.GroundInitialMainSuccessorData

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundRankedExternalSerialization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.GroundInitialMainSuccessorData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD Labels K : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)
local notation "comp" => certificate.compression
local notation "completion" => certificate.compression.born.profiled.heighted.completion
local notation "births" => certificate.births
local notation "heights" => certificate.heights
local notation "external" => certificate.external

theorem exists_rankedExternalSerialization
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    (invariant : source.Invariant K Labels) (level : GroundMainCandidateLevel M K)
    (original : GroundSerializedChronology M (insert source.cutoff source.cutoff) C D rD)
    (originalRank : ZFSet.rank original.code < ZFSet.rank K)
    (originalAgreement : ∀ j s, s ∈ insert source.cutoff source.cutoff →
      original.fields.value j s = source.history.fieldValue j s)
    (prior : GroundSerializedChronology M (insert (comp).born.births.limit (comp).born.births.limit) C D rD)
    (priorRank : ZFSet.rank prior.code < ZFSet.rank K)
    (agreement : ∀ j s, s ∈ insert (comp).born.births.limit (comp).born.births.limit →
      prior.fields.value j s = (comp).history.fieldValue j s) :
    ∃ serial : GroundSerializedChronology M (insert (births).limit (births).limit) C D rD,
      serial.code ∈ M.sets ∧ ZFSet.rank serial.code < ZFSet.rank K ∧
      serial.code ∈ level.validChronologies C D rD ∧
      (∀ j s, s ∈ insert (births).limit (births).limit →
        serial.fields.value j s = (external).history.fieldValue j s) ∧
      serial.layerBound = functionGraphRange
        (chronologyPairs (insert (births).limit (births).limit)) serial.layers := by
  have atBase (j : Fin 5) := agreement j (comp).born.births.limit (ZFSet.mem_insert _ _)
  have sourceValues := (comp).limit_values
  have sourceMatch : prior.fields.value 0 (comp).born.births.limit = (completion).algebra.union.fields 0 ∧
      prior.fields.value 1 (comp).born.births.limit = (completion).algebra.union.fields 1 ∧
      prior.fields.value 2 (comp).born.births.limit = (completion).algebra.union.fields 2 ∧
      prior.fields.value 3 (comp).born.births.limit = (comp).born.births.birth :=
    ⟨(atBase 0).trans sourceValues.1, (atBase 1).trans sourceValues.2.1,
      (atBase 2).trans sourceValues.2.2.1, (atBase 3).trans sourceValues.2.2.2.1⟩
  let fields := (births).serializedFields heights prior (external).inputs
    source.stage.group_code source.stage.action_code pairing unions powers separation infinite
    source.stage.actors_ground source.stage.carrier_ground (ZFSet.mem_insert _ _)
  have values : ∀ j s, s ∈ insert (births).limit (births).limit →
      fields.value j s = (external).history.fieldValue j s := by
    intro j s hs
    rw [(births).serializedFields_value heights prior (external).inputs
      source.stage.group_code source.stage.action_code pairing unions powers separation infinite
      source.stage.actors_ground source.stage.carrier_ground (ZFSet.mem_insert _ _) j hs]
    have oldValue (a : ZFSet.{u}) (before : a ∈ (comp).born.births.limit ∨ a = (comp).born.births.limit) :
        ((births).chronologyFields heights prior.toHistory).fieldValue j a = (external).history.fieldValue j a := by
      have ha : a ∈ insert (comp).born.births.limit (comp).born.births.limit := before.elim
        (fun h => ZFSet.mem_insert_of_mem _ h) (fun h => h.symm ▸ ZFSet.mem_insert _ _)
      have left := (births).chronologyFields_old heights prior.toHistory before
      have right := (external).old_values a before
      have eLeft : ((births).chronologyFields heights prior.toHistory).fieldValue j a = prior.fields.value j a :=
        Fin.cases left.1 (Fin.cases left.2.1 (Fin.cases left.2.2.1
          (Fin.cases left.2.2.2.1 (Fin.cases left.2.2.2.2 (fun i => Fin.elim0 i))))) j
      have eRight : (external).history.fieldValue j a = (comp).history.fieldValue j a :=
        Fin.cases right.1 (Fin.cases right.2.1 (Fin.cases right.2.2.1
          (Fin.cases right.2.2.2.1 (Fin.cases right.2.2.2.2 (fun i => Fin.elim0 i))))) j
      exact eLeft.trans ((agreement j a ha).trans eRight.symm)
    rcases ZFSet.mem_insert_iff.1 hs with rfl | hs
    · have left := (births).chronologyFields_limit heights prior.toHistory
      have right := (external).limit_values
      exact Fin.cases (left.1.trans right.1.symm)
        (Fin.cases (left.2.1.trans right.2.1.symm) (Fin.cases (left.2.2.1.trans right.2.2.1.symm)
          (Fin.cases (left.2.2.2.1.trans right.2.2.2.1.symm)
            (Fin.cases (left.2.2.2.2.trans right.2.2.2.2.symm) (fun i => Fin.elim0 i))))) j
    · rcases ((births).times.mem_limit_iff s).1 hs with before | equal | ⟨n, rfl⟩
      · exact oldValue s (Or.inl before)
      · exact oldValue s (Or.inr equal)
      · have left := (births).chronologyFields_stamp heights prior.toHistory n
        have right := (external).stamp_values n
        exact Fin.cases (left.1.trans right.1.symm)
          (Fin.cases (left.2.1.trans right.2.1.symm) (Fin.cases (left.2.2.1.trans right.2.2.1.symm)
            (Fin.cases (left.2.2.2.1.trans right.2.2.2.1.symm)
              (Fin.cases (left.2.2.2.2.trans right.2.2.2.2.symm) (fun i => Fin.elim0 i))))) j
  have limit := conditions.rank_isLimit pairing unions powers separation infinite hK
  have tasks : ZFSet.rank (source.stage.compressionTasks Labels) < ZFSet.rank K :=
    M.groundEligibleTasks_rank_lt limit source.stage.actors source.stage.order source.stage.meetGraph
      source.stage.action invariant.points_rank invariant.labels_rank
  have graphs := certificate.externalFieldGraphs_rank_lt pairing unions powers separation collection
    infinite hK conditions invariant original originalRank originalAgreement fields values
  have raw := (births).serialized_all_ranked_raw_witnesses heights prior (external).inputs
    source.stage.group_code source.stage.action_code pairing unions powers separation infinite
    source.stage.actors_ground source.stage.carrier_ground (ZFSet.mem_insert _ _)
    priorRank sourceMatch limit (ZFSet.rank_lt_of_mem conditions.2.1)
    tasks invariant.points_rank invariant.actors_rank
  have times := conditions.successor_mem pairing unions powers separation infinite hK
    (certificate.external_limit_mem pairing unions powers separation infinite hK conditions invariant.cutoff_mem)
  obtain ⟨serial, ground, rank, member, _, exactValues, exactRange⟩ :=
    fields.exists_rankedSerialization pairing unions powers separation collection infinite choice
      hK conditions times level (ordinalSetProperty_succ (births).times.ordinal)
      ((births).serializedFields_core heights prior (external).inputs source.stage.group_code source.stage.action_code
        pairing unions powers separation infinite source.stage.actors_ground source.stage.carrier_ground
        (ZFSet.mem_insert _ _)) graphs raw
  exact ⟨serial, ground, rank, member, fun j s hs => (exactValues j s).trans (values j s hs), exactRange⟩

end PartitionPilot.Forcing.GroundInitialMainSuccessorData

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundOmegaOneTaskBearingSuccessorFunction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.GroundInitialMainSuccessorData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD Labels K : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
variable (invariant : source.Invariant K Labels) (level : GroundMainCandidateLevel M K)
local notation "births" => certificate.births
include pairing unions powers separation collection infinite choice hK conditions invariant

theorem exists_rankedTargetSerialization_oai
    (prior : GroundSerializedChronology M (insert source.cutoff source.cutoff) C D rD)
    (priorRank : ZFSet.rank prior.code < ZFSet.rank K)
    (agreement : ∀ j s, s ∈ insert source.cutoff source.cutoff →
      prior.fields.value j s = source.history.fieldValue j s) :
    ∃ serial : GroundSerializedChronology M (insert certificate.target.cutoff certificate.target.cutoff) C D rD,
      serial.code ∈ M.sets ∧ ZFSet.rank serial.code < ZFSet.rank K ∧
      serial.code ∈ level.validChronologies C D rD ∧
      (∀ j s, s ∈ insert certificate.target.cutoff certificate.target.cutoff →
        serial.fields.value j s = certificate.target.history.fieldValue j s) ∧
      serial.fields.value 0 certificate.target.cutoff = certificate.target.stage.carrier ∧
      serial.fields.value 1 certificate.target.cutoff = certificate.target.stage.order ∧
      serial.fields.value 2 certificate.target.cutoff = certificate.target.stage.meetGraph ∧
      serial.fields.value 3 certificate.target.cutoff = certificate.target.birth ∧
      serial.fields.value 4 certificate.target.cutoff = certificate.target.stage.height := by
  obtain ⟨compressionSerial, _, compressionRank, _, compressionValues, _⟩ := certificate.exists_rankedCompressionSerialization
    pairing unions powers separation collection infinite choice hK conditions invariant level prior priorRank agreement
  obtain ⟨externalSerial, _, externalRank, _, externalValues, _⟩ := certificate.exists_rankedExternalSerialization
    pairing unions powers separation collection infinite choice hK conditions invariant level
    prior priorRank agreement compressionSerial compressionRank compressionValues
  obtain ⟨bounded, _, boundedRank, _, values⟩ := certificate.exists_rankedBoundedSerialization
    pairing unions powers separation collection infinite choice hK conditions invariant level
    externalSerial externalRank externalValues
  have times : insert (births).limit (births).limit = insert certificate.target.cutoff certificate.target.cutoff :=
    congrArg (fun t : ZFSet.{u} => insert t t) certificate.target_cutoff.symm
  let serial := bounded.castTime times
  have serialValues : ∀ j s, s ∈ insert certificate.target.cutoff certificate.target.cutoff →
      serial.fields.value j s = certificate.target.history.fieldValue j s := by
    intro j s hs
    rw [GroundSerializedChronology.castTime_value]
    have old := values j s (times.symm ▸ hs)
    have same := GroundChronologicalHistory.fieldValue_eq_of_heq times.symm certificate.target_history j s
    exact old.trans same.symm
  have rank : ZFSet.rank serial.code < ZFSet.rank K := by
    rw [GroundSerializedChronology.castTime_code]
    exact boundedRank
  refine ⟨serial, serial.code_ground pairing, rank,
    level.ranked_mem_validChronologies pairing serial rank, serialValues, ?_, ?_, ?_, ?_, ?_⟩
  · exact (serialValues 0 _ (ZFSet.mem_insert _ _)).trans certificate.target.carrier_eq
  · exact (serialValues 1 _ (ZFSet.mem_insert _ _)).trans certificate.target.order_eq
  · exact (serialValues 2 _ (ZFSet.mem_insert _ _)).trans certificate.target.meet_eq
  · exact serialValues 3 _ (ZFSet.mem_insert _ _)
  · exact (serialValues 4 _ (ZFSet.mem_insert _ _)).trans certificate.target.height_eq

end PartitionPilot.Forcing.GroundInitialMainSuccessorData



end OAI
end

theorem solution.{u} : type_of% @OAI.PartitionPilot.Forcing.GroundInitialMainSuccessorData.exists_rankedTargetSerialization_oai.{u} := @OAI.PartitionPilot.Forcing.GroundInitialMainSuccessorData.exists_rankedTargetSerialization_oai.{u}
