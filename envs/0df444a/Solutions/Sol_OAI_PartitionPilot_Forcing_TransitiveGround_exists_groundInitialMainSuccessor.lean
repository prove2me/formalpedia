-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.TransitiveGround.exists_groundInitialMainSuccessor
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:10:09.442544+00:00
-- url     : https://prove2.me/submissions/13d550b3-22a1-4718-ab23-981c0af89831

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Data.List.Chain
import Mathlib.Data.Prod.Lex
import Mathlib.GroupTheory.CoprodI
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Logic.Relation
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.ZFC.Rank
import Definitions.Def_PartitionPrinciple
import Definitions.Def_OAIQ253P009
import Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_exists_groundInitialExternalBoundedGeometry

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_DenseInterpolation
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps

universe u v w

namespace LinearHeightOrder

variable {A : Type u} (R : LinearHeightOrder A)

theorem weak_refl (x : A) : R.Weak x x := Or.inl rfl

theorem weak_trans {x y z : A} (h : R.Weak x y) (h' : R.Weak y z) : R.Weak x z := by
  rcases h with rfl | h
  · exact h'
  · exact Or.inr (R.lt_weak h h')

theorem list_max (a : A) (xs : List A) :
    ∃ m, (m = a ∨ m ∈ xs) ∧ R.Weak a m ∧ ∀ x ∈ xs, R.Weak x m := by
  induction xs with
  | nil => exact ⟨a, Or.inl rfl, R.weak_refl a, by simp⟩
  | cons x xs ih =>
    rcases ih with ⟨m, hm, ha, hx⟩
    rcases R.compare x m with h | eq | h
    · refine ⟨m, ?_, ha, ?_⟩
      · rcases hm with hm | hm
        · exact Or.inl hm
        · exact Or.inr (List.mem_cons_of_mem x hm)
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact Or.inr h
        · exact hx y hy
    · refine ⟨m, ?_, ha, ?_⟩
      · exact Or.inr (List.mem_cons.mpr (Or.inl eq.symm))
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact Or.inl eq
        · exact hx y hy
    · refine ⟨x, Or.inr (List.mem_cons_self), R.weak_trans ha (Or.inr h), ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact R.weak_refl _
      · exact R.weak_trans (hx y hy) (Or.inr h)

theorem list_min (a : A) (xs : List A) :
    ∃ m, (m = a ∨ m ∈ xs) ∧ R.Weak m a ∧ ∀ x ∈ xs, R.Weak m x := by
  rcases R.reverse.list_max a xs with ⟨m, hm, ha, hx⟩
  refine ⟨m, hm, ?_, ?_⟩
  · rcases ha with eq | h
    · exact Or.inl eq.symm
    · exact Or.inr h
  · intro x h
    rcases hx x h with eq | h'
    · exact Or.inl eq.symm
    · exact Or.inr h'

end LinearHeightOrder

namespace DenseHeightOrder

variable {D : Type v} (R : DenseHeightOrder D)

theorem finite_gap (lo hi : D) (lower upper : List D)
    (gap : R.lt lo hi)
    (lower_hi : ∀ x ∈ lower, R.lt x hi)
    (lo_upper : ∀ y ∈ upper, R.lt lo y)
    (separated : ∀ x ∈ lower, ∀ y ∈ upper, R.lt x y) :
    ∃ z, R.lt lo z ∧ R.lt z hi ∧
      (∀ x ∈ lower, R.lt x z) ∧ (∀ y ∈ upper, R.lt z y) := by
  rcases R.toLinearHeightOrder.list_max lo lower with ⟨a, ha, hlo, hlow⟩
  rcases R.toLinearHeightOrder.list_min hi upper with ⟨b, hb, hhi, hupp⟩
  have ab : R.lt a b := by
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact gap
      · exact lo_upper b hb
    · rcases hb with rfl | hb
      · exact lower_hi a ha
      · exact separated a ha b hb
  rcases R.between a b ab with ⟨z, az, zb⟩
  exact ⟨z, R.weak_lt hlo az, R.lt_weak zb hhi,
    fun x hx => R.weak_lt (hlow x hx) az,
    fun y hy => R.lt_weak zb (hupp y hy)⟩

end DenseHeightOrder

namespace CountableInterpolation

variable {A : Type u} {D : Type v} (S : LinearHeightOrder A)
    (R : DenseHeightOrder D) (enumerate : Nat → A) (lo hi : D)

variable {S R enumerate lo hi}

theorem next_exists {n : Nat} (p : Partial S R enumerate lo hi n) (gap : R.lt lo hi) :
    ∃ z, R.lt lo z ∧ R.lt z hi ∧
      (∀ i, i < n → S.lt (enumerate i) (enumerate n) → R.lt (p.value i) z) ∧
      (∀ i, i < n → S.lt (enumerate n) (enumerate i) → R.lt z (p.value i)) ∧
      (∀ i, i < n → enumerate i = enumerate n → p.value i = z) := by
  classical
  by_cases seen : ∃ i, i < n ∧ enumerate i = enumerate n
  · rcases seen with ⟨j, hj, he⟩
    refine ⟨p.value j, p.lower j hj, p.upper j hj, ?_, ?_, ?_⟩
    · intro i h h'
      exact p.strict i j h hj (he ▸ h')
    · intro i h h'
      exact p.strict j i hj h (he ▸ h')
    · intro i h h'
      exact p.equal i j h hj (h'.trans he.symm)
  · let lowers := ((List.range n).filter (fun i => S.lt (enumerate i) (enumerate n))).map p.value
    let uppers := ((List.range n).filter (fun i => S.lt (enumerate n) (enumerate i))).map p.value
    have lower_spec : ∀ x, x ∈ lowers ↔ ∃ i, i < n ∧ S.lt (enumerate i) (enumerate n) ∧ p.value i = x := by
      intro x
      simp only [lowers, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
      constructor
      · rintro ⟨i, ⟨h, h'⟩, eq⟩
        exact ⟨i, h, h', eq⟩
      · rintro ⟨i, h, h', eq⟩
        exact ⟨i, ⟨h, h'⟩, eq⟩
    have upper_spec : ∀ x, x ∈ uppers ↔ ∃ i, i < n ∧ S.lt (enumerate n) (enumerate i) ∧ p.value i = x := by
      intro x
      simp only [uppers, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
      constructor
      · rintro ⟨i, ⟨h, h'⟩, eq⟩
        exact ⟨i, h, h', eq⟩
      · rintro ⟨i, h, h', eq⟩
        exact ⟨i, ⟨h, h'⟩, eq⟩
    have lh : ∀ x ∈ lowers, R.lt x hi := by
      intro x hx
      rcases (lower_spec x).mp hx with ⟨i, h, _, rfl⟩
      exact p.upper i h
    have lu : ∀ x ∈ uppers, R.lt lo x := by
      intro x hx
      rcases (upper_spec x).mp hx with ⟨i, h, _, rfl⟩
      exact p.lower i h
    have sep : ∀ x ∈ lowers, ∀ y ∈ uppers, R.lt x y := by
      intro x hx y hy
      rcases (lower_spec x).mp hx with ⟨i, h, h', rfl⟩
      rcases (upper_spec y).mp hy with ⟨j, k, k', rfl⟩
      exact p.strict i j h k (S.trans h' k')
    rcases R.finite_gap lo hi lowers uppers gap lh lu sep with ⟨z, hz, zh, hl, hu⟩
    refine ⟨z, hz, zh, ?_, ?_, ?_⟩
    · intro i h h'
      exact hl _ ((lower_spec _).mpr ⟨i, h, h', rfl⟩)
    · intro i h h'
      exact hu _ ((upper_spec _).mpr ⟨i, h, h', rfl⟩)
    · intro i h eq
      exact False.elim (seen ⟨i, h, eq⟩)

end CountableInterpolation

end PartitionPilot.Compression.RecursiveMaps

end

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundPairCompositions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing.FunctionGraphOn

universe u
variable {I f : ZFSet.{u}}

theorem value_mem_doubleUnion (h : FunctionGraphOn I f) (i : {i : ZFSet.{u} // i ∈ I}) :
    h.value i ∈ ⋃₀ ⋃₀ f :=
  pair_second_mem_doubleUnion (h.value_entry i)

end PartitionPilot.Forcing.FunctionGraphOn



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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundIdealProjections
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization Compression Compression.RecursiveMaps SetFormula
universe u

namespace TransitiveGround

theorem idealProjectionGraph_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P L ν e cap : ZFSet.{u}} (hP : P ∈ M.sets) (hL : L ∈ M.sets)
    (hν : ν ∈ M.sets) (he : e ∈ M.sets) (hcap : cap ∈ M.sets) :
    idealProjectionGraph P L ν e cap ∈ M.sets :=
  M.relationCompose_mem pairing unions powers separation hL hL hP
    (M.indexedRelationSection_mem pairing unions powers separation hL hL hν hcap)
    (M.relationConverse_mem pairing unions powers separation hP hL he)

end TransitiveGround

variable {A B : Type u} (s : Presentation A) (t : Presentation B)
variable {P : MeetOrder A} {Q : MeetOrder B} (embedding : IdealEmbedding P Q) (top : A)
variable {ν : ZFSet.{u}}
variable (function : ZFSet.IsFunc (ZFSet.prod t.carrier t.carrier) t.carrier ν)
variable (entries : ∀ x y, ZFSet.pair (ZFSet.pair (t.encode x) (t.encode y))
  (t.encode (Q.meet x y)) ∈ ν)
include function entries

theorem idealProjectionGraph_pair_iff (x : B) (a : A) :
    ZFSet.pair (t.encode x) (s.encode a) ∈ idealProjectionGraph s.carrier t.carrier ν
      (s.graph t embedding.toFun) (t.encode (embedding.toFun top)) ↔
        embedding.projection top x = a := by
  constructor
  · intro entry
    obtain ⟨_, _, z, hz, meet, inverse⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 entry
    have image := ((pair_mem_relationConverse _ _ _ _ _).1 inverse).2.2
    obtain ⟨z', rfl⟩ := (t.mem_carrier z).1 hz
    have imageEq := (s.pair_mem_graph t embedding.toFun a z').1 image
    have rawMeet := ((pair_mem_indexedRelationSection _ _ _ _ _ _).1 meet).2.2
    obtain ⟨v, _, unique⟩ := function.2
      (ZFSet.pair (t.encode (embedding.toFun top)) (t.encode x))
      (ZFSet.pair_mem_prod.2 ⟨t.encode_mem _, t.encode_mem _⟩)
    have eq := t.injective ((unique _ rawMeet).trans (unique _ (entries _ _)).symm)
    apply embedding_injective embedding.toMeetEmbedding
    rw [embedding.projection_spec, imageEq, eq, meet_comm]
  · intro equal
    subst a
    apply (pair_mem_relationCompose _ _ _ _ _ _ _).2
    refine ⟨t.encode_mem x, s.encode_mem _, t.encode (embedding.toFun (embedding.projection top x)),
      t.encode_mem _, ?_, ?_⟩
    · apply (pair_mem_indexedRelationSection _ _ _ _ _ _).2
      refine ⟨t.encode_mem _, t.encode_mem _, ?_⟩
      rw [embedding.projection_spec, meet_comm Q x]
      exact entries _ _
    · exact (pair_mem_relationConverse _ _ _ _ _).2
        ⟨s.encode_mem _, t.encode_mem _, (s.pair_mem_graph t embedding.toFun _ _).2 rfl⟩

theorem idealProjectionGraph_eq :
    idealProjectionGraph s.carrier t.carrier ν (s.graph t embedding.toFun)
      (t.encode (embedding.toFun top)) = t.graph s (embedding.projection top) := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, _, _, a, ha, rfl, _, _⟩ := (mem_relationCompose _ _ _ _ _ _).1 hz
    obtain ⟨x, rfl⟩ := (t.mem_carrier x).1 hx
    obtain ⟨a, rfl⟩ := (s.mem_carrier a).1 ha
    exact (t.pair_mem_graph s _ _ _).2 ((idealProjectionGraph_pair_iff s t embedding top function entries x a).1 hz)
  · intro hz
    obtain ⟨x, rfl⟩ := (t.mem_graph s (embedding.projection top) z).1 hz
    exact (idealProjectionGraph_pair_iff s t embedding top function entries _ _).2 rfl

namespace TransitiveGround

theorem idealProjection_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hP : s.carrier ∈ M.sets) (hL : t.carrier ∈ M.sets) (hν : ν ∈ M.sets)
    (he : s.graph t embedding.toFun ∈ M.sets) :
    t.graph s (embedding.projection top) ∈ M.sets := by
  rw [← idealProjectionGraph_eq s t embedding top function entries]
  exact M.idealProjectionGraph_mem pairing unions powers separation hP hL hν he
    (M.transitive hL (t.encode_mem _))

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_IntervalSequenceFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PartitionPilot.Forcing

universe u

theorem leastIntervalNextCandidate_unique {N A D rA rD e lo hi p c x y : ZFSet.{u}}
    (injection : InjectionCode D ZFSet.omega c)
    (hx : leastIntervalNextCandidate N A D rA rD e lo hi p c x)
    (hy : leastIntervalNextCandidate N A D rA rD e lo hi p c y) : x = y := by
  obtain ⟨xValid, n, hn, xn, leastX⟩ := hx
  obtain ⟨yValid, m, hm, ym, leastY⟩ := hy
  obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
  obtain ⟨l, rfl⟩ := (mem_omega_iff_natSetCode m).1 hm
  rcases lt_trichotomy k l with smaller | equal | larger
  · exact False.elim (leastY x xValid.1 xValid (natSetCode k)
      ((natSetCode_mem_iff k l).2 smaller) xn)
  · subst l
    exact injection.injective x y (natSetCode k) xn ym
  · exact False.elim (leastX y yValid.1 yValid (natSetCode l)
      ((natSetCode_mem_iff l k).2 larger) ym)

theorem leastIntervalNextCandidate_exists_unique {N A D rA rD e lo hi p c : ZFSet.{u}}
    (injection : InjectionCode D ZFSet.omega c)
    (candidate : ∃ y, intervalNextCandidate N A D rA rD e lo hi p y) :
    ∃! y, leastIntervalNextCandidate N A D rA rD e lo hi p c y := by
  classical
  let valid : Nat → Prop := fun n => ∃ y, intervalNextCandidate N A D rA rD e lo hi p y ∧
    ZFSet.pair y (natSetCode n) ∈ c
  have existsValid : ∃ n, valid n := by
    obtain ⟨y, hy⟩ := candidate
    obtain ⟨a, entry, _⟩ := injection.function.2 y hy.1
    have aNat := (ZFSet.pair_mem_prod.1 (injection.function.1 entry)).2
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode a).1 aNat
    exact ⟨n, y, hy, entry⟩
  obtain ⟨y, hy, entry⟩ := Nat.find_spec existsValid
  have selected : leastIntervalNextCandidate N A D rA rD e lo hi p c y := by
    refine ⟨hy, natSetCode (Nat.find existsValid), natSetCode_mem_omega _, entry, ?_⟩
    intro z _ hz m hm smaller
    obtain ⟨k, lower, equal⟩ := (mem_natSetCode m (Nat.find existsValid)).1 hm
    have validK : valid k := ⟨z, hz, equal ▸ smaller⟩
    exact Nat.not_lt_of_ge (Nat.find_min' existsValid validK) lower
  exact ⟨y, selected, fun z hz => leastIntervalNextCandidate_unique injection hz selected⟩

namespace BoundedFormula

open SetFormula

theorem truth_iffFormula {n} (φ ψ : BoundedFormula n) (env : Fin n → ZFSet.{u}) :
    Truth (iffFormula φ ψ) env ↔ (Truth φ env ↔ Truth ψ env) := by
  simp only [iffFormula, Truth, truth_imp]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩

theorem truth_intervalNextCandidateFormula {n} (N A D rA rD e lo hi p y : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (intervalNextCandidateFormula N A D rA rD e lo hi p y) env ↔
      intervalNextCandidate (env N) (env A) (env D) (env rA) (env rD) (env e)
        (env lo) (env hi) (env p) (env y) := by
  simp only [intervalNextCandidateFormula, Truth, truth_pairMembershipFormula,
    truth_imp, truth_iffFormula]
  rfl

theorem truth_leastIntervalNextCandidateFormula {n} (N A D rA rD e lo hi p c y omega : Fin n)
    (env : Fin n → ZFSet.{u}) (hOmega : env omega = ZFSet.omega) :
    Truth (leastIntervalNextCandidateFormula N A D rA rD e lo hi p c y omega) env ↔
      leastIntervalNextCandidate (env N) (env A) (env D) (env rA) (env rD) (env e)
        (env lo) (env hi) (env p) (env c) (env y) := by
  simp only [leastIntervalNextCandidateFormula, Truth, truth_exMem, truth_imp,
    truth_pairMembershipFormula, truth_intervalNextCandidateFormula]
  change (intervalNextCandidate (env N) (env A) (env D) (env rA) (env rD) (env e)
      (env lo) (env hi) (env p) (env y) ∧
    ∃ k ∈ env omega, ZFSet.pair (env y) k ∈ env c ∧
      ∀ z ∈ env D, intervalNextCandidate (env N) (env A) (env D) (env rA) (env rD) (env e)
        (env lo) (env hi) (env p) z → ∀ m ∈ k, ZFSet.pair z m ∉ env c) ↔ _
  rw [hOmega]
  rfl

theorem realize_leastIntervalNextCandidateFormula (M : TransitiveGround.{u}) {n}
    (N A D rA rD e lo hi p c y omega : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) (hOmega : env omega = ZFSet.omega) :
    Realize M.sets (leastIntervalNextCandidateFormula N A D rA rD e lo hi p c y omega).toFormula env ↔
      leastIntervalNextCandidate (env N) (env A) (env D) (env rA) (env rD) (env e)
        (env lo) (env hi) (env p) (env c) (env y) :=
  (realize_toFormula M _ env members).trans
    (truth_leastIntervalNextCandidateFormula N A D rA rD e lo hi p c y omega env hOmega)

end BoundedFormula

namespace TransitiveGround

open SetFormula

theorem realize_intervalSequenceStepFormula (M : TransitiveGround.{u})
    (env : Fin 12 → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (hOmega : env 11 = ZFSet.omega) :
    Realize M.sets intervalSequenceStepFormula env ↔
      leastIntervalNextCandidate (env 0) (env 3) (env 4) (env 5) (env 6) (env 7)
        (env 8) (env 9) (env 1) (env 10) (env 2) :=
  BoundedFormula.realize_leastIntervalNextCandidateFormula M 0 3 4 5 6 7 8 9 1 10 2 11
    env members hOmega

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_FiniteIntervalExtension
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

open Compression.RecursiveMaps
universe u

theorem intervalComparisons_of_preserved {A D rA rD a b z y : ZFSet.{u}}
    (source : StrictLinearOrderCode A rA) (target : StrictLinearOrderCode D rD)
    (ha : a ∈ A) (hb : b ∈ A) (hz : z ∈ D) (hy : y ∈ D)
    (same : a = b → z = y)
    (forward : ZFSet.pair a b ∈ rA → ZFSet.pair z y ∈ rD)
    (backward : ZFSet.pair b a ∈ rA → ZFSet.pair y z ∈ rD) :
    (a = b ↔ z = y) ∧ (ZFSet.pair a b ∈ rA ↔ ZFSet.pair z y ∈ rD) ∧
      (ZFSet.pair b a ∈ rA ↔ ZFSet.pair y z ∈ rD) := by
  refine ⟨⟨same, ?_⟩, ⟨forward, ?_⟩, ⟨backward, ?_⟩⟩
  · intro equal
    rcases source.compare a ha b hb with less | equalSource | more
    · have rel := forward less
      rw [equal] at rel
      exact False.elim (target.irrefl y hy rel)
    · exact equalSource
    · have rel := backward more
      rw [equal] at rel
      exact False.elim (target.irrefl y hy rel)
  · intro rel
    rcases source.compare a ha b hb with less | equal | more
    · exact less
    · rw [same equal] at rel
      exact False.elim (target.irrefl y hy rel)
    · exact False.elim (target.irrefl z hz (target.trans z y z rel (backward more)))
  · intro rel
    rcases source.compare a ha b hb with less | equal | more
    · exact False.elim (target.irrefl y hy (target.trans y z y rel (forward less)))
    · rw [same equal] at rel
      exact False.elim (target.irrefl y hy rel)
    · exact more

theorem finite_intervalNextCandidate_exists
    {A D rA rD e lo hi p : ZFSet.{u}} (n : Nat)
    (code : IntervalSequenceCode (natSetCode n) A D rA rD e lo hi p)
    (enumeration : ZFSet.IsFunc ZFSet.omega A e)
    (source : StrictLinearOrderCode A rA) (target : DenseOrderCode D rD)
    (loD : lo ∈ D) (hiD : hi ∈ D) (gap : ZFSet.pair lo hi ∈ rD) :
    ∃ y, intervalNextCandidate (natSetCode n) A D rA rD e lo hi p y := by
  classical
  let enumerate : Nat → {a : ZFSet.{u} // a ∈ A} := fun k =>
    ⟨Classical.choose (enumeration.2 (natSetCode k) (natSetCode_mem_omega k)),
      (ZFSet.pair_mem_prod.1 (enumeration.1
        (Classical.choose_spec (enumeration.2 (natSetCode k) (natSetCode_mem_omega k))).1)).2⟩
  have enumerateEntry (k : Nat) : ZFSet.pair (natSetCode k) (enumerate k).val ∈ e :=
    (Classical.choose_spec (enumeration.2 (natSetCode k) (natSetCode_mem_omega k))).1
  let value : Nat → {q : ZFSet.{u} // q ∈ D} := fun k =>
    if hk : k < n then
      ⟨Classical.choose (code.function.2 (natSetCode k) ((natSetCode_mem_iff k n).2 hk)),
        (ZFSet.pair_mem_prod.1 (code.function.1
          (Classical.choose_spec (code.function.2 (natSetCode k)
            ((natSetCode_mem_iff k n).2 hk))).1)).2⟩
    else ⟨lo, loD⟩
  have valueEntry (k : Nat) (hk : k < n) :
      ZFSet.pair (natSetCode k) (value k).val ∈ p := by
    dsimp only [value]
    rw [dite_eq_left hk]
    exact (Classical.choose_spec (code.function.2 (natSetCode k)
      ((natSetCode_mem_iff k n).2 hk))).1
  let initial : CountableInterpolation.Partial source.toLinearHeightOrder target.toDenseHeightOrder
      enumerate ⟨lo, loD⟩ ⟨hi, hiD⟩ n := {
    value := value
    lower := fun k hk => (code.inside _ _ (valueEntry k hk)).1
    upper := fun k hk => (code.inside _ _ (valueEntry k hk)).2
    strict := fun i j hi hj less => (code.order _ _ _ _ _ _
      (enumerateEntry i) (enumerateEntry j) (valueEntry i hi) (valueEntry j hj)).1 less
    equal := fun i j hi hj equal => Subtype.ext ((code.agree _ _ _ _ _ _
      (enumerateEntry i) (enumerateEntry j) (valueEntry i hi) (valueEntry j hj)).1
        (congrArg Subtype.val equal)) }
  obtain ⟨y, lower, upper, forward, backward, same⟩ := CountableInterpolation.next_exists initial gap
  refine ⟨y.val, y.property, lower, upper, ?_⟩
  intro i hi a _ b _ z _ ea eb iz
  obtain ⟨k, hk, rfl⟩ := (mem_natSetCode i n).1 hi
  have enumFunction : FunctionGraphOn ZFSet.omega e := ⟨A, enumeration⟩
  have valueFunction : FunctionGraphOn (natSetCode n) p := ⟨D, code.function⟩
  have first : (enumerate k).val = a := enumFunction.unique (enumerateEntry k) ea
  have second : (enumerate n).val = b := enumFunction.unique (enumerateEntry n) eb
  have previous : (value k).val = z := valueFunction.unique (valueEntry k hk) iz
  have comparisons := intervalComparisons_of_preserved source target.toStrictLinearOrderCode
    (enumerate k).property (enumerate n).property (value k).property y.property
    (fun equal => congrArg Subtype.val (same k hk (Subtype.ext equal)))
    (forward k hk) (backward k hk)
  change ((enumerate k).val = (enumerate n).val ↔ (value k).val = y.val) ∧
    (ZFSet.pair (enumerate k).val (enumerate n).val ∈ rA ↔ ZFSet.pair (value k).val y.val ∈ rD) ∧
    (ZFSet.pair (enumerate n).val (enumerate k).val ∈ rA ↔ ZFSet.pair y.val (value k).val ∈ rD)
    at comparisons
  rw [first, second, previous] at comparisons
  exact comparisons

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_IntervalTraceValidity
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

theorem intervalSequence_of_next
    {N A D rA rD e lo hi t : ZFSet.{u}}
    (source : StrictLinearOrderCode A rA) (target : StrictLinearOrderCode D rD)
    (enumeration : ZFSet.IsFunc ZFSet.omega A e)
    (natural : N ⊆ ZFSet.omega) (function : FunctionGraphOn N t)
    (next : ∀ i ∈ N, ∀ y, ZFSet.pair i y ∈ t →
      intervalNextCandidate i A D rA rD e lo hi (graphRestriction i t) y) :
    IntervalSequenceCode N A D rA rD e lo hi t := by
  have functionD : ZFSet.IsFunc N D t := by
    refine ⟨?_, function.to_isFunc.2⟩
    intro w hw
    obtain ⟨i, hiN, y, rfl⟩ := function.shape w hw
    exact ZFSet.pair_mem_prod.2 ⟨hiN, (next i hiN y hw).1⟩
  have pairwise : ∀ i j a b q z,
      ZFSet.pair i a ∈ e → ZFSet.pair j b ∈ e →
      ZFSet.pair i q ∈ t → ZFSet.pair j z ∈ t →
      (a = b ↔ q = z) ∧ (ZFSet.pair a b ∈ rA ↔ ZFSet.pair q z ∈ rD) ∧
        (ZFSet.pair b a ∈ rA ↔ ZFSet.pair z q ∈ rD) := by
    intro i j a b q z ia jb iq jz
    have iN := function.pair_source iq
    have jN := function.pair_source jz
    have aA := (ZFSet.pair_mem_prod.1 (enumeration.1 ia)).2
    have bA := (ZFSet.pair_mem_prod.1 (enumeration.1 jb)).2
    have qD := (ZFSet.pair_mem_prod.1 (functionD.1 iq)).2
    have zD := (ZFSet.pair_mem_prod.1 (functionD.1 jz)).2
    obtain ⟨m, rfl⟩ := (mem_omega_iff_natSetCode i).1 (natural iN)
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode j).1 (natural jN)
    rcases lt_trichotomy m n with earlier | same | later
    · exact (next (natSetCode n) jN z jz).2.2.2
        (natSetCode m) ((natSetCode_mem_iff m n).2 earlier)
        a aA b bA q qD ia jb (pair_mem_graphRestriction.2 ⟨iq,
          (natSetCode_mem_iff m n).2 earlier⟩)
    · subst n
      have equalSource : a = b := (show FunctionGraphOn ZFSet.omega e from ⟨A, enumeration⟩).unique ia jb
      have equalTarget : q = z := function.unique iq jz
      subst b
      subst z
      exact ⟨iff_of_true rfl rfl,
        iff_of_false (source.irrefl a aA) (target.irrefl q qD),
        iff_of_false (source.irrefl a aA) (target.irrefl q qD)⟩
    · have reversed := (next (natSetCode m) iN q iq).2.2.2
        (natSetCode n) ((natSetCode_mem_iff n m).2 later)
        b bA a aA z zD jb ia (pair_mem_graphRestriction.2 ⟨jz,
          (natSetCode_mem_iff n m).2 later⟩)
      exact ⟨by simpa only [eq_comm] using reversed.1, reversed.2.2, reversed.2.1⟩
  refine ⟨functionD, ?_, ?_, ?_⟩
  · intro i y iy
    have candidate := next i (function.pair_source iy) y iy
    exact ⟨candidate.2.1, candidate.2.2.1⟩
  · intro i j a b q z ia jb iq jz
    exact (pairwise i j a b q z ia jb iq jz).1
  · intro i j a b q z ia jb iq jz
    exact (pairwise i j a b q z ia jb iq jz).2.1

end PartitionPilot.Forcing

end

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



namespace PartitionPilot.Forcing

open SetFormula SetRealization
universe u

namespace TransitiveGround

variable (M : TransitiveGround.{u})

theorem exists_ground_intervalSequence
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {A D rA rD e lo hi c : ZFSet.{u}}
    (hA : A ∈ M.sets) (hD : D ∈ M.sets) (hrA : rA ∈ M.sets)
    (hrD : rD ∈ M.sets) (he : e ∈ M.sets) (hc : c ∈ M.sets)
    (source : StrictLinearOrderCode A rA) (target : DenseOrderCode D rD)
    (injection : InjectionCode D ZFSet.omega c)
    (enumeration : ZFSet.IsFunc ZFSet.omega A e)
    (loD : lo ∈ D) (hiD : hi ∈ D) (gap : ZFSet.pair lo hi ∈ rD) :
    ∃ t ∈ M.sets, IntervalSequenceCode ZFSet.omega A D rA rD e lo hi t ∧
      OrdinalRecursionTrace
        (groundRecursionStep M intervalSequenceStepFormula (intervalSequenceParams A D rA rD e lo hi c))
        ZFSet.omega t ∧
      ∀ s, OrdinalRecursionTrace
        (groundRecursionStep M intervalSequenceStepFormula (intervalSequenceParams A D rA rD e lo hi c))
        ZFSet.omega s → s = t := by
  have hw := M.omega_mem separation infinite
  have hlo := M.transitive hD loD
  have hhi := M.transitive hD hiD
  let params := intervalSequenceParams A D rA rD e lo hi c
  have members : ∀ i, params i ∈ M.sets :=
    Fin.cases hA (Fin.cases hD (Fin.cases hrA (Fin.cases hrD (Fin.cases he
      (Fin.cases hlo (Fin.cases hhi (Fin.cases hc (Fin.cases hw (fun i => Fin.elim0 i)))))))))
  have decode (N p y : ZFSet.{u}) (hN : N ∈ M.sets) (hp : p ∈ M.sets) (hy : y ∈ M.sets) :
      Realize M.sets intervalSequenceStepFormula (extend N (extend p (extend y params))) ↔
        leastIntervalNextCandidate N A D rA rD e lo hi p c y :=
    M.realize_intervalSequenceStepFormula (extend N (extend p (extend y params)))
      (Fin.cases hN (Fin.cases hp (Fin.cases hy members))) rfl
  have valid {N p : ZFSet.{u}} (natural : N ⊆ ZFSet.omega)
      (trace : OrdinalRecursionTrace (groundRecursionStep M intervalSequenceStepFormula params) N p) :
      IntervalSequenceCode N A D rA rD e lo hi p := by
    apply intervalSequence_of_next source target.toStrictLinearOrderCode enumeration natural trace.1
    intro i hiN y entry
    have step := trace.2 i hiN y entry
    exact ((decode i (graphRestriction i p) y (M.transitive hw (natural hiN))
      step.1 step.2.1).1 step.2.2).1
  have closure : GroundOrdinalStepClosure M ZFSet.omega intervalSequenceStepFormula params := by
    intro N hN p hp trace
    have hNM := M.transitive hw hN
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode N).1 hN
    have natural : natSetCode n ⊆ (ZFSet.omega : ZFSet.{u}) := by
      intro i hiN
      obtain ⟨k, _, rfl⟩ := (mem_natSetCode i n).1 hiN
      exact natSetCode_mem_omega k
    have prefixValid := valid natural trace
    have candidate := finite_intervalNextCandidate_exists n prefixValid enumeration source target
      loD hiD gap
    obtain ⟨y, selected, unique⟩ := leastIntervalNextCandidate_exists_unique injection candidate
    have hy := M.transitive hD selected.1.1
    exact ⟨y, hy, (decode _ p y hNM hp hy).2 selected,
      fun z hz relation => unique z ((decode _ p z hNM hp hz).1 relation)⟩
  have ordinal : ordinalSetProperty (ZFSet.omega : ZFSet.{u}) := by
    rw [← ordinalCode_omega]
    exact ordinalSetProperty_ordinalCode Ordinal.omega0
  obtain ⟨t, ht, trace, unique, _⟩ := M.exists_unique_ordinalRecursionTrace
    pairing unions separation collection hw ordinal intervalSequenceStepFormula params members closure
  exact ⟨t, ht, valid (fun _ hi => hi) trace, trace, unique⟩

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_IntervalEmbeddingFamilyCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing

universe u

theorem leastInjectionMember_unique {A f d b : ZFSet.{u}}
    (injection : InjectionCode A ZFSet.omega f)
    (hd : leastInjectionMember A f d) (hb : leastInjectionMember A f b) : d = b := by
  obtain ⟨dA, n, hn, dn, leastD⟩ := hd
  obtain ⟨bA, m, hm, bm, leastB⟩ := hb
  obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
  obtain ⟨l, rfl⟩ := (mem_omega_iff_natSetCode m).1 hm
  rcases lt_trichotomy k l with smaller | equal | larger
  · exact False.elim (leastB d dA (natSetCode k) ((natSetCode_mem_iff k l).2 smaller) dn)
  · subst l
    exact injection.injective d b (natSetCode k) dn bm
  · exact False.elim (leastD b bA (natSetCode l) ((natSetCode_mem_iff l k).2 larger) bm)

theorem leastInjectionMember_exists_unique {A f : ZFSet.{u}}
    (injection : InjectionCode A ZFSet.omega f) (nonempty : A.Nonempty) :
    ∃! d, leastInjectionMember A f d := by
  classical
  let valid : Nat → Prop := fun n => ∃ d ∈ A, ZFSet.pair d (natSetCode n) ∈ f
  have existsValid : ∃ n, valid n := by
    obtain ⟨d, hd⟩ := nonempty
    obtain ⟨n, entry, _⟩ := injection.function.2 d hd
    obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode n).1
      (ZFSet.pair_mem_prod.1 (injection.function.1 entry)).2
    exact ⟨k, d, hd, entry⟩
  obtain ⟨d, hd, entry⟩ := Nat.find_spec existsValid
  have selected : leastInjectionMember A f d := by
    refine ⟨hd, natSetCode (Nat.find existsValid), natSetCode_mem_omega _, entry, ?_⟩
    intro x hx m hm smaller
    obtain ⟨k, lower, equal⟩ := (mem_natSetCode m (Nat.find existsValid)).1 hm
    have validK : valid k := ⟨x, hx, equal ▸ smaller⟩
    exact Nat.not_lt_of_ge (Nat.find_min' existsValid validK) lower
  exact ⟨d, selected, fun b hb => leastInjectionMember_unique injection hb selected⟩

theorem canonicalEnumerationDefault_least {A f : ZFSet.{u}}
    (injection : InjectionCode A ZFSet.omega f) (nonempty : A.Nonempty) :
    leastInjectionMember A f (canonicalEnumerationDefault A f) := by
  classical
  have existsDefault := (leastInjectionMember_exists_unique injection nonempty).exists
  simpa only [canonicalEnumerationDefault, dite_eq_left existsDefault] using Classical.choose_spec existsDefault

theorem canonicalEnumeration_isFunc {A f : ZFSet.{u}}
    (injection : InjectionCode A ZFSet.omega f) (nonempty : A.Nonempty) :
    ZFSet.IsFunc ZFSet.omega A (canonicalEnumeration A f) :=
  defaultInverse_isFunc injection (canonicalEnumerationDefault_least injection nonempty).1

theorem canonicalEnumeration_onto {A f : ZFSet.{u}}
    (injection : InjectionCode A ZFSet.omega f) :
    ∀ a ∈ A, ∃ n ∈ ZFSet.omega, ZFSet.pair n a ∈ canonicalEnumeration A f :=
  defaultInverse_onto injection (canonicalEnumerationDefault A f)

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem canonicalEnumerationDefault_mem {A f : ZFSet.{u}} (hA : A ∈ M.sets)
    (injection : InjectionCode A ZFSet.omega f) (nonempty : A.Nonempty) :
    canonicalEnumerationDefault A f ∈ M.sets :=
  M.transitive hA (canonicalEnumerationDefault_least injection nonempty).1

theorem canonicalEnumeration_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A f : ZFSet.{u}} (hA : A ∈ M.sets) (hf : f ∈ M.sets) (hOmega : ZFSet.omega ∈ M.sets)
    (injection : InjectionCode A ZFSet.omega f) (nonempty : A.Nonempty) :
    canonicalEnumeration A f ∈ M.sets :=
  M.defaultInverse_mem pairing unions powers separation hA hOmega hf
    (M.canonicalEnumerationDefault_mem hA injection nonempty)

end TransitiveGround






theorem intervalSequenceGraph_subset (A D e t : ZFSet.{u}) :
    intervalSequenceGraph A D e t ⊆ ZFSet.prod A D :=
  fun _ hz => (ZFSet.mem_sep.1 hz).1

theorem mem_intervalSequenceGraph (A D e t z : ZFSet.{u}) :
    z ∈ intervalSequenceGraph A D e t ↔
      ∃ n ∈ ZFSet.omega, ∃ a ∈ A, ∃ q ∈ D,
        z = ZFSet.pair a q ∧ ZFSet.pair n a ∈ e ∧ ZFSet.pair n q ∈ t := by
  constructor
  · exact fun h => (ZFSet.mem_sep.1 h).2
  · rintro ⟨n, hn, a, ha, q, hq, rfl, en, tn⟩
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2 ⟨ha, hq⟩, n, hn, a, ha, q, hq, rfl, en, tn⟩

theorem pair_mem_intervalSequenceGraph (A D e t a q : ZFSet.{u}) :
    ZFSet.pair a q ∈ intervalSequenceGraph A D e t ↔
      a ∈ A ∧ q ∈ D ∧ ∃ n ∈ ZFSet.omega, ZFSet.pair n a ∈ e ∧ ZFSet.pair n q ∈ t := by
  rw [mem_intervalSequenceGraph]
  constructor
  · rintro ⟨n, hn, b, hb, z, hz, equal, en, tn⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hb, hz, n, hn, en, tn⟩
  · rintro ⟨ha, hq, n, hn, en, tn⟩
    exact ⟨n, hn, a, ha, q, hq, rfl, en, tn⟩

theorem intervalSequenceGraph_isFunc {A D rA rD e lo hi t : ZFSet.{u}}
    (code : IntervalSequenceCode ZFSet.omega A D rA rD e lo hi t)
    (onto : ∀ a ∈ A, ∃ n ∈ ZFSet.omega, ZFSet.pair n a ∈ e) :
    ZFSet.IsFunc A D (intervalSequenceGraph A D e t) := by
  refine ⟨intervalSequenceGraph_subset A D e t, ?_⟩
  intro a ha
  obtain ⟨n, hn, en⟩ := onto a ha
  obtain ⟨q, tn, _⟩ := code.function.2 n hn
  have hq := (ZFSet.pair_mem_prod.1 (code.function.1 tn)).2
  refine ⟨q, (pair_mem_intervalSequenceGraph A D e t a q).2 ⟨ha, hq, n, hn, en, tn⟩, ?_⟩
  intro z hz
  obtain ⟨_, _, m, _, em, tm⟩ := (pair_mem_intervalSequenceGraph A D e t a z).1 hz
  exact (code.agree m n a a z q em en tm tn).1 rfl

theorem intervalSequenceGraph_injection {A D rA rD e lo hi t : ZFSet.{u}}
    (code : IntervalSequenceCode ZFSet.omega A D rA rD e lo hi t)
    (onto : ∀ a ∈ A, ∃ n ∈ ZFSet.omega, ZFSet.pair n a ∈ e) :
    InjectionCode A D (intervalSequenceGraph A D e t) := by
  refine ⟨intervalSequenceGraph_isFunc code onto, ?_⟩
  intro a b q ha hb
  obtain ⟨_, _, n, _, en, tn⟩ := (pair_mem_intervalSequenceGraph A D e t a q).1 ha
  obtain ⟨_, _, m, _, em, tm⟩ := (pair_mem_intervalSequenceGraph A D e t b q).1 hb
  exact (code.agree n m a b q q en em tn tm).2 rfl

theorem intervalSequenceGraph_order_iff {A D rA rD e lo hi t a b q z : ZFSet.{u}}
    (code : IntervalSequenceCode ZFSet.omega A D rA rD e lo hi t)
    (ha : ZFSet.pair a q ∈ intervalSequenceGraph A D e t)
    (hb : ZFSet.pair b z ∈ intervalSequenceGraph A D e t) :
    ZFSet.pair q z ∈ rD ↔ ZFSet.pair a b ∈ rA := by
  obtain ⟨_, _, n, _, en, tn⟩ := (pair_mem_intervalSequenceGraph A D e t a q).1 ha
  obtain ⟨_, _, m, _, em, tm⟩ := (pair_mem_intervalSequenceGraph A D e t b z).1 hb
  exact (code.order n m a b q z en em tn tm).symm

theorem intervalSequenceGraph_inside {A D rA rD e lo hi t a q : ZFSet.{u}}
    (code : IntervalSequenceCode ZFSet.omega A D rA rD e lo hi t)
    (entry : ZFSet.pair a q ∈ intervalSequenceGraph A D e t) :
    ZFSet.pair lo q ∈ rD ∧ ZFSet.pair q hi ∈ rD := by
  obtain ⟨_, _, n, _, _, tn⟩ := (pair_mem_intervalSequenceGraph A D e t a q).1 entry
  exact code.inside n q tn






namespace BoundedFormula

open SetFormula

theorem truth_intervalSequenceEntryFormula {n} (z a d e t omega : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (intervalSequenceEntryFormula z a d e t omega) env ↔
      ∃ i ∈ env omega, ∃ x ∈ env a, ∃ q ∈ env d,
        env z = ZFSet.pair x q ∧ ZFSet.pair i x ∈ env e ∧ ZFSet.pair i q ∈ env t := by
  simp only [intervalSequenceEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_pairMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem intervalSequenceGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A D e t : ZFSet.{u}} (hA : A ∈ M.sets) (hD : D ∈ M.sets)
    (he : e ∈ M.sets) (ht : t ∈ M.sets) (hOmega : ZFSet.omega ∈ M.sets) :
    intervalSequenceGraph A D e t ∈ M.sets := by
  let params := extend A (extend D (extend e (extend t (extend ZFSet.omega Fin.elim0))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.intervalSequenceEntryFormula 0 1 2 3 4 5) params
    (Fin.cases hA (Fin.cases hD (Fin.cases he (Fin.cases ht
      (Fin.cases hOmega (fun i => Fin.elim0 i))))))
    (M.prod_mem pairing unions powers separation hA hD)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.intervalSequenceEntryFormula 0 1 2 3 4 5) (extend z params))
      (ZFSet.prod A D) = intervalSequenceGraph A D e t := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, intervalSequenceGraph, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_intervalSequenceEntryFormula 0 1 2 3 4 5 _)
  exact equal ▸ selected

theorem intervalSequenceDescent_spec
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A D rA rD e lo hi t : ZFSet.{u}} (hA : A ∈ M.sets) (hD : D ∈ M.sets)
    (he : e ∈ M.sets) (ht : t ∈ M.sets) (hOmega : ZFSet.omega ∈ M.sets)
    (code : IntervalSequenceCode ZFSet.omega A D rA rD e lo hi t)
    (onto : ∀ a ∈ A, ∃ n ∈ ZFSet.omega, ZFSet.pair n a ∈ e) :
    intervalSequenceGraph A D e t ∈ M.sets ∧
      InjectionCode A D (intervalSequenceGraph A D e t) ∧
      (∀ a q, ZFSet.pair a q ∈ intervalSequenceGraph A D e t →
        ZFSet.pair lo q ∈ rD ∧ ZFSet.pair q hi ∈ rD) ∧
      (∀ a b q z, ZFSet.pair a q ∈ intervalSequenceGraph A D e t →
        ZFSet.pair b z ∈ intervalSequenceGraph A D e t →
        (ZFSet.pair q z ∈ rD ↔ ZFSet.pair a b ∈ rA)) :=
  ⟨M.intervalSequenceGraph_mem pairing unions powers separation hA hD he ht hOmega,
    intervalSequenceGraph_injection code onto,
    fun _ _ entry => intervalSequenceGraph_inside code entry,
    fun _ _ _ _ left right => intervalSequenceGraph_order_iff code left right⟩

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing

open SetFormula SetRealization Compression.RecursiveMaps.RationalHeights
universe u

theorem intervalEmbeddingCode_empty (D rA rD lo hi : ZFSet.{u}) :
    IntervalEmbeddingCode ∅ D rA rD lo hi ∅ := by
  refine ⟨⟨⟨ZFSet.empty_subset _, fun a ha => False.elim (ZFSet.notMem_empty a ha)⟩, ?_⟩, ?_, ?_⟩
  · intro a b q entry _
    exact False.elim (ZFSet.notMem_empty _ entry)
  · intro a b q z entry _
    exact False.elim (ZFSet.notMem_empty _ entry)
  · intro a q entry
    exact False.elim (ZFSet.notMem_empty _ entry)

namespace TransitiveGround

variable (M : TransitiveGround.{u})

theorem exists_intervalEmbedding_of_enumeration
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {A D rA rD e lo hi c : ZFSet.{u}}
    (hA : A ∈ M.sets) (hD : D ∈ M.sets) (hrA : rA ∈ M.sets)
    (hrD : rD ∈ M.sets) (he : e ∈ M.sets) (hc : c ∈ M.sets)
    (source : StrictLinearOrderCode A rA) (target : DenseOrderCode D rD)
    (injection : InjectionCode D ZFSet.omega c)
    (enumeration : ZFSet.IsFunc ZFSet.omega A e)
    (onto : ∀ a ∈ A, ∃ n ∈ ZFSet.omega, ZFSet.pair n a ∈ e)
    (loD : lo ∈ D) (hiD : hi ∈ D) (gap : ZFSet.pair lo hi ∈ rD) :
    ∃ f ∈ M.sets, IntervalEmbeddingCode A D rA rD lo hi f := by
  obtain ⟨t, ht, sequence, _, _⟩ := M.exists_ground_intervalSequence
    pairing unions separation collection infinite hA hD hrA hrD he hc
    source target injection enumeration loD hiD gap
  obtain ⟨member, inj, inside, order⟩ := M.intervalSequenceDescent_spec
    pairing unions powers separation hA hD he ht (M.omega_mem separation infinite) sequence onto
  exact ⟨intervalSequenceGraph A D e t, member, inj,
    fun a b q z first second => (order a b q z first second).symm, inside⟩

theorem exists_intervalEmbedding
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {A D rA rD lo hi c : ZFSet.{u}}
    (hA : A ∈ M.sets) (hD : D ∈ M.sets) (hrA : rA ∈ M.sets)
    (hrD : rD ∈ M.sets) (hc : c ∈ M.sets)
    (source : StrictLinearOrderCode A rA) (target : DenseOrderCode D rD)
    (injection : InjectionCode D ZFSet.omega c)
    (small : M.groundEmbeddable A ZFSet.omega)
    (loD : lo ∈ D) (hiD : hi ∈ D) (gap : ZFSet.pair lo hi ∈ rD) :
    ∃ f ∈ M.sets, IntervalEmbeddingCode A D rA rD lo hi f := by
  by_cases nonempty : A.Nonempty
  · obtain ⟨sourceCode, hSourceCode, sourceInjection⟩ := small
    have he := M.canonicalEnumeration_mem pairing unions powers separation
      hA hSourceCode (M.omega_mem separation infinite) sourceInjection nonempty
    have enumeration := canonicalEnumeration_isFunc sourceInjection nonempty
    have onto := canonicalEnumeration_onto sourceInjection
    exact M.exists_intervalEmbedding_of_enumeration pairing unions powers separation collection infinite
      hA hD hrA hrD he hc source target injection enumeration onto loD hiD gap
  · have empty : A = ∅ := by
      apply ZFSet.ext
      intro a
      exact ⟨fun ha => False.elim (nonempty ⟨a, ha⟩), fun ha => False.elim (ZFSet.notMem_empty a ha)⟩
    exact ⟨∅, M.empty_mem ⟨D, hD⟩, empty ▸ intervalEmbeddingCode_empty D rA rD lo hi⟩

end TransitiveGround

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

theorem heightOrderRestriction_linear {B R r : ZFSet.{u}}
    (linear : StrictLinearOrderCode B r) (subset : R ⊆ B) :
    StrictLinearOrderCode R (heightOrderRestriction R r) := by
  refine ⟨fun _ h => (ZFSet.mem_sep.1 h).2, ?_, ?_, ?_⟩
  · intro a ha entry
    exact linear.irrefl a (subset ha) (ZFSet.mem_sep.1 entry).1
  · intro a b c first second
    obtain ⟨ab, ha, _⟩ := (pair_mem_heightOrderRestriction R r a b).1 first
    obtain ⟨bc, _, hc⟩ := (pair_mem_heightOrderRestriction R r b c).1 second
    exact (pair_mem_heightOrderRestriction R r a c).2 ⟨linear.trans a b c ab bc, ha, hc⟩
  · intro a ha b hb
    rcases linear.compare a (subset ha) b (subset hb) with ab | equal | ba
    · exact Or.inl ((pair_mem_heightOrderRestriction R r a b).2 ⟨ab, ha, hb⟩)
    · exact Or.inr (Or.inl equal)
    · exact Or.inr (Or.inr ((pair_mem_heightOrderRestriction R r b a).2 ⟨ba, hb, ha⟩))

theorem function_on_relationImage {A B h : ZFSet.{u}} (function : ZFSet.IsFunc A B h) :
    ZFSet.IsFunc A (relationImage A B h) h := by
  refine ⟨?_, function.2⟩
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := ZFSet.mem_prod.1 (function.1 hz)
  exact ZFSet.pair_mem_prod.2 ⟨ha, (mem_relationImage A B h b).2 ⟨hb, a, ha, hz⟩⟩

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundCountableProducts
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

theorem countableProduct_injection
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {A B f g : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets)
    (hf : f ∈ M.sets) (hg : g ∈ M.sets)
    (first : InjectionCode A ZFSet.omega f) (second : InjectionCode B ZFSet.omega g) :
    ∃ h ∈ M.sets, InjectionCode (ZFSet.prod A B) ZFSet.omega h := by
  have hw := M.omega_mem separation infinite
  have hAB := M.prod_mem pairing unions powers separation hA hB
  have hww := M.prod_mem pairing unions powers separation hw hw
  have product := M.relationProduct_mem pairing unions powers separation hA hB hw hw hf hg
  obtain ⟨c, hc, pairingCode⟩ := M.omega_product_countable pairing unions powers separation infinite
  exact ⟨relationCompose (ZFSet.prod A B) (ZFSet.prod ZFSet.omega ZFSet.omega) ZFSet.omega
      (relationProduct A B ZFSet.omega ZFSet.omega f g) c,
    M.relationCompose_mem pairing unions powers separation hAB hww hw product hc,
    (relationProduct_injection first second).compose pairingCode⟩

theorem groundEmbeddable_product
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {A B : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets)
    (first : M.groundEmbeddable A ZFSet.omega) (second : M.groundEmbeddable B ZFSet.omega) :
    M.groundEmbeddable (ZFSet.prod A B) ZFSet.omega := by
  obtain ⟨f, hf, firstCode⟩ := first
  obtain ⟨g, hg, secondCode⟩ := second
  exact M.countableProduct_injection pairing unions powers separation infinite hA hB hf hg firstCode secondCode

end TransitiveGround

end PartitionPilot.Forcing

end

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundLiftedRowTupleProvenance
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

theorem pairedGraph_eq {A B C : Type u} (s : Presentation A) (t : Presentation B)
    (v : Presentation C) (f : A → B) (g : A → C) :
    pairedGraph s.carrier t.carrier v.carrier (s.graph t f) (s.graph v g) =
      s.graph (t.product v) (fun x => (f x, g x)) := by
  apply ZFSet.ext
  intro z
  rw [mem_pairedGraph, Presentation.mem_graph]
  constructor
  · rintro ⟨x, hx, a, ha, b, hb, rfl, first, second⟩
    obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨a, rfl⟩ := (t.mem_carrier a).1 ha
    obtain ⟨b, rfl⟩ := (v.mem_carrier b).1 hb
    have fa := (s.pair_mem_graph t f x a).1 first
    have gb := (s.pair_mem_graph v g x b).1 second
    exact ⟨x, congrArg (ZFSet.pair (s.encode x)) (congrArg₂ ZFSet.pair (congrArg t.encode fa) (congrArg v.encode gb))⟩
  · rintro ⟨x, rfl⟩
    exact ⟨s.encode x, s.encode_mem x, t.encode (f x), t.encode_mem _, v.encode (g x), v.encode_mem _, rfl,
      (s.pair_mem_graph t f _ _).2 rfl, (s.pair_mem_graph v g _ _).2 rfl⟩

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

theorem pushedHeightGraph_range {A B H e h : ZFSet.{u}}
    (embedding : InjectionCode A B e) (height : ZFSet.IsFunc A H h) :
    relationImage (relationImage A B e) H (pushedHeightGraph A B H e h) = relationImage A H h := by
  apply ZFSet.ext
  intro z
  rw [mem_relationImage, mem_relationImage]
  constructor
  · rintro ⟨hz, y, hy, entry⟩
    obtain ⟨_, x, hx, copy⟩ := (mem_relationImage A B e y).1 hy
    exact ⟨hz, x, hx, (pushedHeightGraph_entry embedding height copy).1 entry⟩
  · rintro ⟨hz, x, hx, entry⟩
    obtain ⟨y, copy, _⟩ := embedding.function.2 x hx
    have hy := (ZFSet.pair_mem_prod.1 (embedding.function.1 copy)).2
    exact ⟨hz, y, (mem_relationImage A B e y).2 ⟨hy, x, hx, copy⟩,
      (pushedHeightGraph_entry embedding height copy).2 entry⟩

theorem pushedHeightGraph_strictLex {A B C D rA rB μA μB e h rD : ZFSet.{u}}
    (embedding : IdealEmbeddingCode A B rA rB μA μB e)
    (height : StrictLexHeightCode A C D rA h rD) :
    StrictLexHeightCode (relationImage A B e) C D rB (pushedHeightGraph A B (ZFSet.prod C D) e h) rD := by
  refine ⟨pushedHeightGraph_function embedding.injection height.function, ?_⟩
  intro x hx y hy c q d v lower different first second
  obtain ⟨_, a, ha, ax⟩ := (mem_relationImage A B e x).1 hx
  obtain ⟨_, b, hb, by'⟩ := (mem_relationImage A B e y).1 hy
  have distinct : a ≠ b := by
    intro same
    subst b
    obtain ⟨_, _, unique⟩ := embedding.injection.function.2 a ha
    exact different ((unique x ax).trans (unique y by').symm)
  exact height.strict a ha b hb c q d v (embedding.reflect a b x y ax by' lower) distinct
    ((pushedHeightGraph_entry embedding.injection height.function ax).1 first)
    ((pushedHeightGraph_entry embedding.injection height.function by').1 second)

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundCompressionHeightSteps
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

open Compression.RecursiveMaps
universe u

namespace BoundedFormula

theorem truth_lexHeightEntryFormula {n} (z C D rD : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (lexHeightEntryFormula z C D rD) env ↔
      ∃ c ∈ env C, ∃ q ∈ env D, ∃ d ∈ env C, ∃ v ∈ env D,
        env z = ZFSet.pair (ZFSet.pair c q) (ZFSet.pair d v) ∧
          (c ∈ d ∨ (c = d ∧ ZFSet.pair q v ∈ env rD)) := by
  simp only [lexHeightEntryFormula, truth_exMem, Truth, truth_disj,
    truth_pairOfPairsFormula, truth_pairMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula

theorem lexHeightOrder_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {C D rD : ZFSet.{u}} (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) :
    lexHeightOrder C D rD ∈ M.sets := by
  have carrier := M.prod_mem pairing unions powers separation hC hD
  let params := extend C (extend D (extend rD Fin.elim0))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.lexHeightEntryFormula 0 1 2 3) params
    (Fin.cases hC (Fin.cases hD (Fin.cases hrD (fun i => Fin.elim0 i))))
    (M.prod_mem pairing unions powers separation carrier carrier)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.lexHeightEntryFormula 0 1 2 3) (extend z params))
      (ZFSet.prod (ZFSet.prod C D) (ZFSet.prod C D)) = lexHeightOrder C D rD := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, lexHeightOrder, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_lexHeightEntryFormula 0 1 2 3 _)
  exact equal ▸ selected

end TransitiveGround






end PartitionPilot.Forcing



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

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_OwnerBirthLayers
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

theorem ownerBirthGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P B T old levels stamps : ZFSet.{u}}
    (hP : P ∈ M.sets) (hB : B ∈ M.sets) (hT : T ∈ M.sets)
    (hOld : old ∈ M.sets) (hLevels : levels ∈ M.sets) (hStamps : stamps ∈ M.sets)
    (hOmega : ZFSet.omega ∈ M.sets) :
    ownerBirthGraph P B T old levels stamps ∈ M.sets := by
  exact M.binary_union_mem pairing unions hOld
    (M.relationCompose_mem pairing unions powers separation
      (M.ownerFresh_mem separation hP hB) hOmega hT hLevels hStamps)

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing
universe u

theorem ownerBirthGraph_oldMeet {P B r μ T T0 old levels stamps : ZFSet.{u}}
    (meet : MeetOrderCode B r μ) (oldFunction : ZFSet.IsFunc P T0 old)
    (oldSubset : P ⊆ B) (times : T0 ⊆ T)
    (levelFunction : ZFSet.IsFunc (ownerFresh P B) ZFSet.omega levels)
    (stampCode : OwnerStampCode T stamps)
    (oldMeet : OldMeetCode r μ old)
    (oldIdeal : ∀ x ∈ B, ∀ y ∈ P, ZFSet.pair x y ∈ r → x ∈ P)
    (oldBefore : ∀ x a n t, ZFSet.pair x a ∈ old →
      ZFSet.pair (natSetCode n) t ∈ stamps → a ∈ t)
    (levelMono : ∀ x ∈ ownerFresh P B, ∀ y ∈ ownerFresh P B, ∀ n m,
      ZFSet.pair x (natSetCode n) ∈ levels → ZFSet.pair y (natSetCode m) ∈ levels →
      ZFSet.pair x y ∈ r → n ≤ m) :
    OldMeetCode r μ (ownerBirthGraph P B T old levels stamps) := by
  have born := ownerBirthGraph_function oldFunction oldSubset times levelFunction stampCode.function
  intro x y z a b c ya xb before notLower xy zc
  have hy := (ZFSet.pair_mem_prod.1 (born.1 ya)).1
  have hz := (ZFSet.pair_mem_prod.1 (born.1 zc)).1
  by_cases xOld : x ∈ P
  · have xbOld := (ownerBirthGraph_old_iff xOld).1 xb
    by_cases yOld : y ∈ P
    · have zOld := oldIdeal z hz x xOld (meet.lower_left x y z xy)
      exact oldMeet x y z a b c ((ownerBirthGraph_old_iff yOld).1 ya) xbOld before notLower xy
        ((ownerBirthGraph_old_iff zOld).1 zc)
    · obtain ⟨_, _, m, _, stampY⟩ := (ownerBirthGraph_fresh_nat_iff oldFunction yOld).1 ya
      exact (ZFSet.mem_asymm before (oldBefore x b m a xbOld stampY)).elim
  · obtain ⟨_, _, n, _, stampX⟩ := (ownerBirthGraph_fresh_nat_iff oldFunction xOld).1 xb
    by_cases zOld : z ∈ P
    · exact oldBefore z c n b ((ownerBirthGraph_old_iff zOld).1 zc) stampX
    · have yOld : y ∉ P := fun member => zOld (oldIdeal z hz y member (meet.lower_right x y z xy))
      obtain ⟨_, _, m, levelY, stampY⟩ := (ownerBirthGraph_fresh_nat_iff oldFunction yOld).1 ya
      obtain ⟨_, _, k, levelZ, stampZ⟩ := (ownerBirthGraph_fresh_nat_iff oldFunction zOld).1 zc
      have lowerLevels := levelMono z ((mem_ownerFresh P B z).2 ⟨hz, zOld⟩)
        y ((mem_ownerFresh P B y).2 ⟨hy, yOld⟩) k m levelZ levelY (meet.lower_right x y z xy)
      exact (stampCode.strict k n c b stampZ stampX).2
        (Nat.lt_of_le_of_lt lowerLevels ((stampCode.strict m n a b stampY stampX).1 before))

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundCodedBinaryHeights
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

theorem StrictLexHeightCode.strictHeightGraph {L C D r h rD : ZFSet.{u}}
    (code : StrictLexHeightCode L C D r h rD) :
    StrictHeightGraphCode L (ZFSet.prod C D) r (lexHeightOrder C D rD) h := by
  refine ⟨code.function, ?_⟩
  intro x hx y hy different lower a b first second
  obtain ⟨c, hc, q, hq, eq⟩ := ZFSet.mem_prod.1 (ZFSet.pair_mem_prod.1 (code.function.1 first)).2
  obtain ⟨d, hd, v, hv, eq'⟩ := ZFSet.mem_prod.1 (ZFSet.pair_mem_prod.1 (code.function.1 second)).2
  subst a
  subst b
  exact (pair_mem_lexHeightOrder _ _ _ _ _ _ _).2
    ⟨hc, hq, hd, hv, code.strict x hx y hy c q d v lower different first second⟩

namespace TransitiveGround

theorem exists_groundHeightInterpolation (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {L H rL rH seed D rD c lo hi : ZFSet.{u}}
    (hL : L ∈ M.sets) (hH : H ∈ M.sets) (hrH : rH ∈ M.sets) (hSeed : seed ∈ M.sets)
    (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) (hc : c ∈ M.sets)
    (seedCode : StrictHeightGraphCode L H rL rH seed)
    (linear : StrictLinearOrderCode H rH) (target : DenseOrderCode D rD)
    (injection : InjectionCode D ZFSet.omega c)
    (small : M.groundEmbeddable (relationImage L H seed) ZFSet.omega)
    (hlo : lo ∈ D) (hhi : hi ∈ D) (gap : ZFSet.pair lo hi ∈ rD) :
    ∃ height ∈ M.sets, StrictHeightGraphCode L D rL rD height ∧
      (∀ x z, ZFSet.pair x z ∈ height → ZFSet.pair lo z ∈ rD ∧ ZFSet.pair z hi ∈ rD) ∧
      relationImage L D height ∈ M.sets ∧
      M.groundEmbeddable (relationImage L D height) ZFSet.omega ∧
      ∀ x y a b q z, ZFSet.pair x a ∈ seed → ZFSet.pair y b ∈ seed →
        ZFSet.pair x q ∈ height → ZFSet.pair y z ∈ height →
          (a = b ↔ q = z) ∧ (ZFSet.pair a b ∈ rH ↔ ZFSet.pair q z ∈ rD) := by
  let R := relationImage L H seed
  have hR := M.relationImage_mem separation hL hH hSeed
  have hOrder : heightOrderRestriction R rH ∈ M.sets :=
    M.injection_restriction_mem separation hR hR hrH
  have rLinear : StrictLinearOrderCode R (heightOrderRestriction R rH) :=
    heightOrderRestriction_linear linear (fun _ h => ((mem_relationImage L H seed _).1 h).1)
  obtain ⟨e, he, embedding⟩ := M.exists_intervalEmbedding pairing unions powers separation collection infinite
    hR hD hOrder hrD hc rLinear target injection small hlo hhi gap
  let height := relationCompose L R D seed e
  have function := relationCompose_function_of_subset (function_on_relationImage seedCode.function)
    embedding.injection.function (fun _ h => h)
  have ground : height ∈ M.sets := M.relationCompose_mem pairing unions powers separation hL hR hD hSeed he
  have liftEntry {x a z : ZFSet.{u}} (source : ZFSet.pair x a ∈ seed)
      (entry : ZFSet.pair x z ∈ height) : ZFSet.pair a z ∈ e := by
    obtain ⟨_, _, a', _, other, image⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 entry
    obtain ⟨v, _, unique⟩ := seedCode.function.2 x (ZFSet.pair_mem_prod.1 (seedCode.function.1 source)).1
    have equal := (unique a source).trans (unique a' other).symm
    exact equal.symm ▸ image
  have exactOrder {x y a b q z : ZFSet.{u}}
      (first : ZFSet.pair x a ∈ seed) (second : ZFSet.pair y b ∈ seed)
      (left : ZFSet.pair x q ∈ height) (right : ZFSet.pair y z ∈ height) :
      (a = b ↔ q = z) ∧ (ZFSet.pair a b ∈ rH ↔ ZFSet.pair q z ∈ rD) := by
    have aq := liftEntry first left
    have bz := liftEntry second right
    have aR := (ZFSet.pair_mem_prod.1 (embedding.injection.function.1 aq)).1
    have bR := (ZFSet.pair_mem_prod.1 (embedding.injection.function.1 bz)).1
    refine ⟨?_, ?_⟩
    · constructor
      · intro equal
        subst b
        obtain ⟨v, _, unique⟩ := embedding.injection.function.2 a aR
        exact (unique q aq).trans (unique z bz).symm
      · intro equal
        subst z
        exact embedding.injection.injective a b q aq bz
    · have order := embedding.order a b q z aq bz
      rw [pair_mem_heightOrderRestriction] at order
      exact ⟨fun hab => order.1 ⟨hab, aR, bR⟩, fun hqz => (order.2 hqz).1⟩
  refine ⟨height, ground, ⟨function, ?_⟩, ?_, M.relationImage_mem separation hL hD ground, ?_, ?_⟩
  · intro x hx y hy different lower q z left right
    obtain ⟨a, ax, _⟩ := seedCode.function.2 x hx
    obtain ⟨b, byEntry, _⟩ := seedCode.function.2 y hy
    exact (exactOrder ax byEntry left right).2.1 (seedCode.strict x hx y hy different lower a b ax byEntry)
  · intro x z entry
    obtain ⟨_, _, a, _, _, az⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 entry
    exact embedding.inside a z az
  · exact M.groundEmbeddable_restrict separation (M.relationImage_mem separation hL hD ground)
      (M.omega_mem separation infinite) (fun _ h => (mem_relationImage _ _ _ _).1 h |>.1) ⟨c, hc, injection⟩
  · intro x y a b q z first second left right
    exact exactOrder first second left right

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open Compression.RecursiveMaps
universe u

theorem mem_lexProductOrder (C D rC rD z : ZFSet.{u}) :
    z ∈ lexProductOrder C D rC rD ↔
      ∃ c ∈ C, ∃ q ∈ D, ∃ d ∈ C, ∃ v ∈ D,
        z = ZFSet.pair (ZFSet.pair c q) (ZFSet.pair d v) ∧
          (ZFSet.pair c d ∈ rC ∨ (c = d ∧ ZFSet.pair q v ∈ rD)) := by
  constructor
  · exact fun h => (ZFSet.mem_sep.1 h).2
  · rintro ⟨c, hc, q, hq, d, hd, v, hv, rfl, lower⟩
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2
      ⟨ZFSet.pair_mem_prod.2 ⟨hc, hq⟩, ZFSet.pair_mem_prod.2 ⟨hd, hv⟩⟩,
      c, hc, q, hq, d, hd, v, hv, rfl, lower⟩

theorem pair_mem_lexProductOrder (C D rC rD c q d v : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair c q) (ZFSet.pair d v) ∈ lexProductOrder C D rC rD ↔
      c ∈ C ∧ q ∈ D ∧ d ∈ C ∧ v ∈ D ∧ (ZFSet.pair c d ∈ rC ∨ (c = d ∧ ZFSet.pair q v ∈ rD)) := by
  rw [mem_lexProductOrder]
  constructor
  · rintro ⟨c', hc, q', hq, d', hd, v', hv, equal, lower⟩
    obtain ⟨left, right⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 left
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 right
    exact ⟨hc, hq, hd, hv, lower⟩
  · rintro ⟨hc, hq, hd, hv, lower⟩
    exact ⟨c, hc, q, hq, d, hd, v, hv, rfl, lower⟩

theorem lexProductOrder_code {C D rC rD : ZFSet.{u}}
    (columns : StrictLinearOrderCode C rC) (target : StrictLinearOrderCode D rD) :
    StrictLinearOrderCode (ZFSet.prod C D) (lexProductOrder C D rC rD) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_, ?_, ?_⟩
  · intro x hx hxx
    obtain ⟨c, _, q, hq, rfl⟩ := ZFSet.mem_prod.1 hx
    rcases ((pair_mem_lexProductOrder C D rC rD c q c q).1 hxx).2.2.2.2 with less | same
    · exact columns.irrefl c (ZFSet.pair_mem_prod.1 (columns.shape less)).1 less
    · exact target.irrefl q hq same.2
  · intro x y z hxy hyz
    have xy := ZFSet.pair_mem_prod.1 (ZFSet.mem_sep.1 hxy).1
    have yz := ZFSet.pair_mem_prod.1 (ZFSet.mem_sep.1 hyz).1
    obtain ⟨c, hc, q, hq, rfl⟩ := ZFSet.mem_prod.1 xy.1
    obtain ⟨d, _, v, _, rfl⟩ := ZFSet.mem_prod.1 xy.2
    obtain ⟨b, hb, w, hw, rfl⟩ := ZFSet.mem_prod.1 yz.2
    have left := ((pair_mem_lexProductOrder C D rC rD c q d v).1 hxy).2.2.2.2
    have right := ((pair_mem_lexProductOrder C D rC rD d v b w).1 hyz).2.2.2.2
    apply (pair_mem_lexProductOrder C D rC rD c q b w).2
    refine ⟨hc, hq, hb, hw, ?_⟩
    rcases left with lower | ⟨same, inside⟩
    · rcases right with lower' | ⟨same', _⟩
      · exact Or.inl (columns.trans c d b lower lower')
      · exact Or.inl (same' ▸ lower)
    · rcases right with lower' | ⟨same', inside'⟩
      · exact Or.inl (same.symm ▸ lower')
      · exact Or.inr ⟨same.trans same', target.trans q v w inside inside'⟩
  · intro x hx y hy
    obtain ⟨c, hc, q, hq, rfl⟩ := ZFSet.mem_prod.1 hx
    obtain ⟨d, hd, v, hv, rfl⟩ := ZFSet.mem_prod.1 hy
    rcases columns.compare c hc d hd with lower | same | greater
    · exact Or.inl ((pair_mem_lexProductOrder C D rC rD c q d v).2 ⟨hc, hq, hd, hv, Or.inl lower⟩)
    · subst d
      rcases target.compare q hq v hv with lower | same | greater
      · exact Or.inl ((pair_mem_lexProductOrder C D rC rD c q c v).2
          ⟨hc, hq, hc, hv, Or.inr ⟨rfl, lower⟩⟩)
      · exact Or.inr (Or.inl (congrArg (ZFSet.pair c) same))
      · exact Or.inr (Or.inr ((pair_mem_lexProductOrder C D rC rD c v c q).2
          ⟨hc, hv, hc, hq, Or.inr ⟨rfl, greater⟩⟩))
    · exact Or.inr (Or.inr ((pair_mem_lexProductOrder C D rC rD d v c q).2
        ⟨hd, hv, hc, hq, Or.inl greater⟩))

namespace BoundedFormula

theorem truth_lexProductEntryFormula {n} (z C D rC rD : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (lexProductEntryFormula z C D rC rD) env ↔
      ∃ c ∈ env C, ∃ q ∈ env D, ∃ d ∈ env C, ∃ v ∈ env D,
        env z = ZFSet.pair (ZFSet.pair c q) (ZFSet.pair d v) ∧
          (ZFSet.pair c d ∈ env rC ∨ (c = d ∧ ZFSet.pair q v ∈ env rD)) := by
  simp only [lexProductEntryFormula, truth_exMem, Truth, truth_disj,
    truth_pairOfPairsFormula, truth_pairMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula

theorem lexProductOrder_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {C D rC rD : ZFSet.{u}} (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrC : rC ∈ M.sets) (hrD : rD ∈ M.sets) :
    lexProductOrder C D rC rD ∈ M.sets := by
  have carrier := M.prod_mem pairing unions powers separation hC hD
  let params := extend C (extend D (extend rC (extend rD Fin.elim0)))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.lexProductEntryFormula 0 1 2 3 4) params
    (Fin.cases hC (Fin.cases hD (Fin.cases hrC (Fin.cases hrD (fun i => Fin.elim0 i)))))
    (M.prod_mem pairing unions powers separation carrier carrier)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.lexProductEntryFormula 0 1 2 3 4) (extend z params))
      (ZFSet.prod (ZFSet.prod C D) (ZFSet.prod C D)) = lexProductOrder C D rC rD := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, lexProductOrder, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_lexProductEntryFormula 0 1 2 3 4 _)
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing


section

namespace PartitionPilot.Forcing
open SetRealization Compression.RecursiveMaps SetFormula
universe u

theorem StrictHeightGraphCode.smallHeight_graph {L H rL rH h μ : ZFSet.{u}}
    (code : StrictHeightGraphCode L H rL rH h) (meet : MeetOrderCode L rL μ)
    (linear : StrictLinearOrderCode H rH) :
    (SetMembers.presentation L).graph (SetMembers.presentation H) (code.smallHeight meet linear).value = h :=
  (SetMembers.presentation L).graph_decodeFunction (SetMembers.presentation H) h code.function

end PartitionPilot.Forcing

namespace PartitionPilot.SetRealization.Presentation
open Forcing Compression.RecursiveMaps
universe u
variable {A B C : Type u}

theorem strictHeightGraphCode (s : Presentation A) (t : Presentation B)
    {P : MeetOrder A} {R : HeightOrder B} (height : StrictHeight P R)
    {r rH : ZFSet.{u}}
    (order : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ r ↔ P.le x y)
    (target : ∀ a b, ZFSet.pair (t.encode a) (t.encode b) ∈ rH ↔ R.lt a b) :
    StrictHeightGraphCode s.carrier t.carrier r rH (s.graph t height.value) := by
  refine ⟨s.graph_isFunc t height.value, ?_⟩
  intro x hx y hy different lower a b first second
  obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 hx
  obtain ⟨y, rfl⟩ := (s.mem_carrier y).1 hy
  obtain ⟨a, rfl⟩ := (t.mem_carrier a).1 (ZFSet.pair_mem_prod.1 ((s.graph_isFunc t height.value).1 first)).2
  obtain ⟨b, rfl⟩ := (t.mem_carrier b).1 (ZFSet.pair_mem_prod.1 ((s.graph_isFunc t height.value).1 second)).2
  have firstEq := (s.pair_mem_graph t height.value x a).1 first
  have secondEq := (s.pair_mem_graph t height.value y b).1 second
  rw [← firstEq, ← secondEq]
  exact (target _ _).2 (height.strict x y ((order x y).1 lower) (fun eq => different (congrArg s.encode eq)))

theorem lexProductOrder_iff (s : Presentation A) (t : Presentation B)
    (R : LinearHeightOrder A) (S : LinearHeightOrder B) {rR rS : ZFSet.{u}}
    (first : ∀ a b, ZFSet.pair (s.encode a) (s.encode b) ∈ rR ↔ R.lt a b)
    (second : ∀ a b, ZFSet.pair (t.encode a) (t.encode b) ∈ rS ↔ S.lt a b) (x y : A × B) :
    ZFSet.pair ((s.product t).encode x) ((s.product t).encode y) ∈
      lexProductOrder s.carrier t.carrier rR rS ↔ (R.lex S).lt x y := by
  change ZFSet.pair (ZFSet.pair (s.encode x.1) (t.encode x.2))
    (ZFSet.pair (s.encode y.1) (t.encode y.2)) ∈ _ ↔ _
  rw [pair_mem_lexProductOrder]
  simp only [s.encode_mem, t.encode_mem, true_and, first, second, s.injective.eq_iff]
  rfl

theorem compose_graphs (s : Presentation A) (t : Presentation B) (v : Presentation C)
    (f : A → B) (g : B → C) :
    relationCompose s.carrier t.carrier v.carrier (s.graph t f) (t.graph v g) =
      s.graph v (fun x => g (f x)) := by
  apply ZFSet.ext
  intro z
  rw [mem_relationCompose, Presentation.mem_graph]
  constructor
  · rintro ⟨x, hx, y, hy, w, hw, rfl, first, second⟩
    obtain ⟨a, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨b, rfl⟩ := (t.mem_carrier y).1 hy
    obtain ⟨c, rfl⟩ := (v.mem_carrier w).1 hw
    have ab := (s.pair_mem_graph t f a b).1 first
    have bc := (t.pair_mem_graph v g b c).1 second
    subst b
    subst c
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨s.encode a, s.encode_mem a, t.encode (f a), t.encode_mem _,
      v.encode (g (f a)), v.encode_mem _, rfl,
      (s.pair_mem_graph t f _ _).2 rfl, (t.pair_mem_graph v g _ _).2 rfl⟩

end PartitionPilot.SetRealization.Presentation

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable {A B C : Type u} (s : Presentation A) (t : Presentation B) (v : Presentation C)

include pairing unions powers separation

theorem composed_graph_mem (f : A → B) (g : B → C)
    (hs : s.carrier ∈ M.sets) (ht : t.carrier ∈ M.sets) (hv : v.carrier ∈ M.sets)
    (hf : s.graph t f ∈ M.sets) (hg : t.graph v g ∈ M.sets) :
    s.graph v (fun x => g (f x)) ∈ M.sets := by
  rw [← s.compose_graphs t v f g]
  exact M.relationCompose_mem pairing unions powers separation hs ht hv hf hg

theorem paired_graph_mem (f : A → B) (g : A → C)
    (hs : s.carrier ∈ M.sets) (ht : t.carrier ∈ M.sets) (hv : v.carrier ∈ M.sets)
    (hf : s.graph t f ∈ M.sets) (hg : s.graph v g ∈ M.sets) :
    s.graph (t.product v) (fun x => (f x, g x)) ∈ M.sets := by
  rw [← pairedGraph_eq s t v f g]
  exact M.pairedGraph_mem pairing unions powers separation hs ht hv hf hg

end PartitionPilot.Forcing.TransitiveGround

end


namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization Compression.RecursiveMaps SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
variable {A H : Type u} (s : Presentation A) (t : Presentation H)
variable {P : MeetOrder A} (top : A) (greatest : ∀ a, P.le a top)
variable (R : LinearHeightOrder H) (seed : StrictHeight P R.toHeightOrder)
variable (hP : s.carrier ∈ M.sets) (hH : t.carrier ∈ M.sets)
variable (hSeed : s.graph t seed.value ∈ M.sets)
variable (small : M.groundEmbeddable (relationImage s.carrier t.carrier (s.graph t seed.value)) ZFSet.omega)

include pairing unions powers separation infinite hP hH hSeed small

theorem binaryTuple_ground (tile : TileRequests.Tile P (ULift.{u} Unit))
    (q : Presentation tile.Space) {ν : ZFSet.{u}}
    (hL : q.carrier ∈ M.sets) (hν : ν ∈ M.sets)
    (meetFunction : ZFSet.IsFunc (ZFSet.prod q.carrier q.carrier) q.carrier ν)
    (meetEntries : ∀ x y, ZFSet.pair (ZFSet.pair (q.encode x) (q.encode y))
      (q.encode (tile.order.meet x y)) ∈ ν)
    (root : s.graph q tile.root.toFun ∈ M.sets)
    (child : s.graph q (tile.child ⟨()⟩).toFun ∈ M.sets) :
    let graph := q.graph (t.product t) (tile.binaryTuple top greatest R seed).value
    graph ∈ M.sets ∧ M.groundEmbeddable
      (relationImage q.carrier (t.product t).carrier graph) ZFSet.omega := by
  dsimp only
  have first := M.idealProjection_mem s q tile.root top meetFunction meetEntries
    pairing unions powers separation hP hL hν root
  have second := M.idealProjection_mem s q (tile.child ⟨()⟩) top meetFunction meetEntries
    pairing unions powers separation hP hL hν child
  have firstHeight := M.composed_graph_mem pairing unions powers separation q s t
    (tile.root.projection top) seed.value hL hP hH first hSeed
  have secondHeight := M.composed_graph_mem pairing unions powers separation q s t
    ((tile.child ⟨()⟩).projection top) seed.value hL hP hH second hSeed
  have graphGround : q.graph (t.product t) (tile.binaryTuple top greatest R seed).value ∈ M.sets :=
    M.paired_graph_mem pairing unions powers separation q t t _ _ hL hH hH firstHeight secondHeight
  refine ⟨graphGround, ?_⟩
  let E := relationImage s.carrier t.carrier (s.graph t seed.value)
  have hE : E ∈ M.sets := M.relationImage_mem separation hP hH hSeed
  have each (a : A) : t.encode (seed.value a) ∈ E :=
    (mem_relationImage _ _ _ _).2 ⟨t.encode_mem _, s.encode a, s.encode_mem a,
      (s.pair_mem_graph t seed.value _ _).2 rfl⟩
  apply M.groundEmbeddable_restrict separation
    (M.relationImage_mem separation hL (M.prod_mem pairing unions powers separation hH hH) graphGround)
    (M.omega_mem separation infinite) ?_
    (M.groundEmbeddable_product pairing unions powers separation infinite hE hE small small)
  intro z hz
  obtain ⟨_, x, hx, entry⟩ := (mem_relationImage _ _ _ _).1 hz
  obtain ⟨x, rfl⟩ := (q.mem_carrier x).1 hx
  obtain ⟨y, eq⟩ := (q.mem_graph (t.product t) (tile.binaryTuple top greatest R seed).value _).1 entry
  have parts := ZFSet.pair_inj.1 eq
  have xy := q.injective parts.1
  subst y
  rw [← parts.2]
  exact ZFSet.pair_mem_prod.2 ⟨each _, each _⟩

theorem rectangleTuple_ground (tile : TileRequests.Tile P (ULift.{u} Bool))
    (q : Presentation tile.Space) {ν : ZFSet.{u}}
    (hL : q.carrier ∈ M.sets) (hν : ν ∈ M.sets)
    (meetFunction : ZFSet.IsFunc (ZFSet.prod q.carrier q.carrier) q.carrier ν)
    (meetEntries : ∀ x y, ZFSet.pair (ZFSet.pair (q.encode x) (q.encode y))
      (q.encode (tile.order.meet x y)) ∈ ν)
    (root : s.graph q tile.root.toFun ∈ M.sets)
    (first : s.graph q (tile.child ⟨false⟩).toFun ∈ M.sets)
    (second : s.graph q (tile.child ⟨true⟩).toFun ∈ M.sets) :
    let graph := q.graph (t.product (t.product t)) (tile.rectangleTuple top greatest R seed).value
    graph ∈ M.sets ∧ M.groundEmbeddable
      (relationImage q.carrier (t.product (t.product t)).carrier graph) ZFSet.omega := by
  dsimp only
  have project (e : IdealEmbedding P tile.order) (he : s.graph q e.toFun ∈ M.sets) :=
    M.composed_graph_mem pairing unions powers separation q s t (e.projection top) seed.value
      hL hP hH (M.idealProjection_mem s q e top meetFunction meetEntries
        pairing unions powers separation hP hL hν he) hSeed
  have pairGround := M.paired_graph_mem pairing unions powers separation q t t _ _ hL hH hH
    (project (tile.child ⟨false⟩) first) (project (tile.child ⟨true⟩) second)
  have hHH := M.prod_mem pairing unions powers separation hH hH
  have graphGround : q.graph (t.product (t.product t)) (tile.rectangleTuple top greatest R seed).value ∈ M.sets :=
    M.paired_graph_mem pairing unions powers separation q t (t.product t) _ _ hL hH hHH
      (project tile.root root) pairGround
  refine ⟨graphGround, ?_⟩
  let E := relationImage s.carrier t.carrier (s.graph t seed.value)
  have hE : E ∈ M.sets := M.relationImage_mem separation hP hH hSeed
  have each (a : A) : t.encode (seed.value a) ∈ E :=
    (mem_relationImage _ _ _ _).2 ⟨t.encode_mem _, s.encode a, s.encode_mem a,
      (s.pair_mem_graph t seed.value _ _).2 rfl⟩
  have smallEE := M.groundEmbeddable_product pairing unions powers separation infinite hE hE small small
  have smallEEE := M.groundEmbeddable_product pairing unions powers separation infinite hE
    (M.prod_mem pairing unions powers separation hE hE) small smallEE
  apply M.groundEmbeddable_restrict separation
    (M.relationImage_mem separation hL (M.prod_mem pairing unions powers separation hH hHH) graphGround)
    (M.omega_mem separation infinite) ?_ smallEEE
  intro z hz
  obtain ⟨_, x, hx, entry⟩ := (mem_relationImage _ _ _ _).1 hz
  obtain ⟨x, rfl⟩ := (q.mem_carrier x).1 hx
  obtain ⟨y, eq⟩ := (q.mem_graph (t.product (t.product t)) (tile.rectangleTuple top greatest R seed).value _).1 entry
  have parts := ZFSet.pair_inj.1 eq
  have xy := q.injective parts.1
  subst y
  rw [← parts.2]
  exact ZFSet.pair_mem_prod.2 ⟨each _, ZFSet.pair_mem_prod.2 ⟨each _, each _⟩⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetRealization Compression.RecursiveMaps SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
variable {A H : Type u} (s : Presentation A) (t : Presentation H)
variable {P : MeetOrder A} (top : A) (greatest : ∀ a, P.le a top)
variable (R : LinearHeightOrder H) (seed : StrictHeight P R.toHeightOrder)
variable {rH D rD c lo hi : ZFSet.{u}}
variable (heightOrder : ∀ a b, ZFSet.pair (t.encode a) (t.encode b) ∈ rH ↔ R.lt a b)
variable (linear : StrictLinearOrderCode t.carrier rH)
variable (target : DenseOrderCode D rD) (injection : InjectionCode D ZFSet.omega c)
variable (hP : s.carrier ∈ M.sets) (hH : t.carrier ∈ M.sets)
variable (hSeed : s.graph t seed.value ∈ M.sets) (hrH : rH ∈ M.sets)
variable (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) (hc : c ∈ M.sets)
variable (small : M.groundEmbeddable (relationImage s.carrier t.carrier (s.graph t seed.value)) ZFSet.omega)
variable (hlo : lo ∈ D) (hhi : hi ∈ D) (gap : ZFSet.pair lo hi ∈ rD)
include top greatest pairing unions powers separation collection infinite heightOrder linear target injection
  hP hH hSeed hrH hD hrD hc small hlo hhi gap

theorem exists_binaryTileIntervalHeight (tile : TileRequests.Tile P (ULift.{u} Unit))
    (q : Presentation tile.Space) {r ν : ZFSet.{u}}
    (hL : q.carrier ∈ M.sets) (hν : ν ∈ M.sets)
    (related : ∀ x y, ZFSet.pair (q.encode x) (q.encode y) ∈ r ↔ tile.order.le x y)
    (meetFunction : ZFSet.IsFunc (ZFSet.prod q.carrier q.carrier) q.carrier ν)
    (meetEntries : ∀ x y, ZFSet.pair (ZFSet.pair (q.encode x) (q.encode y))
      (q.encode (tile.order.meet x y)) ∈ ν)
    (root : s.graph q tile.root.toFun ∈ M.sets)
    (child : s.graph q (tile.child ⟨()⟩).toFun ∈ M.sets) :
    ∃ height ∈ M.sets, IntervalHeightCode q.carrier r D rD lo hi height ∧
      relationImage q.carrier D height ∈ M.sets ∧
      M.groundEmbeddable (relationImage q.carrier D height) ZFSet.omega := by
  have tuple := M.binaryTuple_ground pairing unions powers separation infinite s t top greatest R seed
    hP hH hSeed small tile q hL hν meetFunction meetEntries root child
  have strict := q.strictHeightGraphCode (t.product t) (tile.binaryTuple top greatest R seed) related
    (t.lexProductOrder_iff t R R heightOrder heightOrder)
  obtain ⟨height, ground, code, inside, rangeGround, rangeSmall, _⟩ :=
    M.exists_groundHeightInterpolation pairing unions powers separation collection infinite hL
      (M.prod_mem pairing unions powers separation hH hH)
      (M.lexProductOrder_mem pairing unions powers separation hH hH hrH hrH) tuple.1
      hD hrD hc strict (lexProductOrder_code linear linear) target injection tuple.2 hlo hhi gap
  exact ⟨height, ground, ⟨code, inside⟩, rangeGround, rangeSmall⟩

theorem exists_rectangleTileIntervalHeight (tile : TileRequests.Tile P (ULift.{u} Bool))
    (q : Presentation tile.Space) {r ν : ZFSet.{u}}
    (hL : q.carrier ∈ M.sets) (hν : ν ∈ M.sets)
    (related : ∀ x y, ZFSet.pair (q.encode x) (q.encode y) ∈ r ↔ tile.order.le x y)
    (meetFunction : ZFSet.IsFunc (ZFSet.prod q.carrier q.carrier) q.carrier ν)
    (meetEntries : ∀ x y, ZFSet.pair (ZFSet.pair (q.encode x) (q.encode y))
      (q.encode (tile.order.meet x y)) ∈ ν)
    (root : s.graph q tile.root.toFun ∈ M.sets)
    (first : s.graph q (tile.child ⟨false⟩).toFun ∈ M.sets)
    (second : s.graph q (tile.child ⟨true⟩).toFun ∈ M.sets) :
    ∃ height ∈ M.sets, IntervalHeightCode q.carrier r D rD lo hi height ∧
      relationImage q.carrier D height ∈ M.sets ∧
      M.groundEmbeddable (relationImage q.carrier D height) ZFSet.omega := by
  have tuple := M.rectangleTuple_ground pairing unions powers separation infinite s t top greatest R seed
    hP hH hSeed small tile q hL hν meetFunction meetEntries root first second
  have inner := t.lexProductOrder_iff t R R heightOrder heightOrder
  have strict := q.strictHeightGraphCode (t.product (t.product t)) (tile.rectangleTuple top greatest R seed) related
    (t.lexProductOrder_iff (t.product t) R (R.lex R) heightOrder inner)
  have hHH := M.prod_mem pairing unions powers separation hH hH
  have hrHH := M.lexProductOrder_mem pairing unions powers separation hH hH hrH hrH
  obtain ⟨height, ground, code, inside, rangeGround, rangeSmall, _⟩ :=
    M.exists_groundHeightInterpolation pairing unions powers separation collection infinite hL
      (M.prod_mem pairing unions powers separation hH hHH)
      (M.lexProductOrder_mem pairing unions powers separation hH hHH hrH hrHH) tuple.1
      hD hrD hc strict (lexProductOrder_code linear (lexProductOrder_code linear linear))
      target injection tuple.2 hlo hhi gap
  exact ⟨height, ground, ⟨code, inside⟩, rangeGround, rangeSmall⟩

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization Compression.RecursiveMaps SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
variable {A H : Type u} (s : Presentation A) (t : Presentation H)
variable {P : MeetOrder A} (top : A) (greatest : ∀ a, P.le a top)
variable (R : LinearHeightOrder H) (seed : StrictHeight P R.toHeightOrder)
variable {rH D rD c lo hi : ZFSet.{u}}
variable (heightOrder : ∀ a b, ZFSet.pair (t.encode a) (t.encode b) ∈ rH ↔ R.lt a b)
variable (linear : StrictLinearOrderCode t.carrier rH)
variable (target : DenseOrderCode D rD) (injection : InjectionCode D ZFSet.omega c)
variable (hP : s.carrier ∈ M.sets) (hH : t.carrier ∈ M.sets)
variable (hSeed : s.graph t seed.value ∈ M.sets) (hrH : rH ∈ M.sets)
variable (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) (hc : c ∈ M.sets)
variable (small : M.groundEmbeddable (relationImage s.carrier t.carrier (s.graph t seed.value)) ZFSet.omega)
variable (hlo : lo ∈ D) (hhi : hi ∈ D) (gap : ZFSet.pair lo hi ∈ rD)
include top greatest pairing unions powers separation collection infinite heightOrder linear target injection
  hP hH hSeed hrH hD hrD hc small hlo hhi gap

theorem exists_requestTileIntervalHeight (request : TileRequests.Request P)
    (q : Presentation (request.tile top greatest).Space) {r ν : ZFSet.{u}}
    (hL : q.carrier ∈ M.sets) (hν : ν ∈ M.sets)
    (related : ∀ x y, ZFSet.pair (q.encode x) (q.encode y) ∈ r ↔ (request.tile top greatest).order.le x y)
    (meetFunction : ZFSet.IsFunc (ZFSet.prod q.carrier q.carrier) q.carrier ν)
    (meetEntries : ∀ x y, ZFSet.pair (ZFSet.pair (q.encode x) (q.encode y))
      (q.encode ((request.tile top greatest).order.meet x y)) ∈ ν)
    (root : s.graph q (request.tile top greatest).root.toFun ∈ M.sets)
    (children : ∀ j, s.graph q ((request.tile top greatest).child j).toFun ∈ M.sets) :
    ∃ height ∈ M.sets, IntervalHeightCode q.carrier r D rD lo hi height ∧
      relationImage q.carrier D height ∈ M.sets ∧
      M.groundEmbeddable (relationImage q.carrier D height) ZFSet.omega := by
  cases request with
  | separation W =>
    exact M.exists_binaryTileIntervalHeight pairing unions powers separation collection infinite s t top greatest R seed
      heightOrder linear target injection hP hH hSeed hrH hD hrD hc small hlo hhi gap
      _ q hL hν related meetFunction meetEntries root (children ⟨()⟩)
  | compression K copy =>
    exact M.exists_binaryTileIntervalHeight pairing unions powers separation collection infinite s t top greatest R seed
      heightOrder linear target injection hP hH hSeed hrH hD hrD hc small hlo hhi gap
      _ q hL hν related meetFunction meetEntries root (children ⟨()⟩)
  | rectangle data =>
    exact M.exists_rectangleTileIntervalHeight pairing unions powers separation collection infinite s t top greatest R seed
      heightOrder linear target injection hP hH hSeed hrH hD hrD hc small hlo hhi gap
      _ q hL hν related meetFunction meetEntries root (children ⟨false⟩) (children ⟨true⟩)

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
universe u

theorem pair_mem_intervalHeightRelation (I W Ps rs D rD lo hi i f : ZFSet.{u}) :
    ZFSet.pair i f ∈ intervalHeightRelation I W Ps rs D rD lo hi ↔
      i ∈ I ∧ f ∈ W ∧ intervalHeightCandidate Ps rs D rD lo hi i f := by
  rw [intervalHeightRelation, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hi, hf⟩, j, _, g, _, equal, valid⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hi, hf, valid⟩
  · rintro ⟨hi, hf, valid⟩
    exact ⟨⟨hi, hf⟩, i, hi, f, hf, rfl, valid⟩

theorem intervalHeightCandidate_iff {I Ps rs D rD lo hi : ZFSet.{u}}
    (sources : FunctionGraphOn I Ps) (orders : FunctionGraphOn I rs)
    (i : {i : ZFSet.{u} // i ∈ I}) (f : ZFSet.{u}) :
    intervalHeightCandidate Ps rs D rD lo hi i.val f ↔
      IntervalHeightCode (sources.value i) (orders.value i) D rD lo hi f := by
  constructor
  · rintro ⟨P, _, r, _, pEntry, rEntry, code⟩
    rw [sources.value_eq_of_entry i pEntry, orders.value_eq_of_entry i rEntry]
    exact code
  · intro code
    exact ⟨sources.value i, sources.value_mem_doubleUnion i,
      orders.value i, orders.value_mem_doubleUnion i,
      sources.value_entry i, orders.value_entry i, code⟩

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_ExternalColumnCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization Compression.RecursiveMaps
universe u

theorem successorColumnGraph_injection {C base sequence : ZFSet.{u}}
    (function : ZFSet.IsFunc ZFSet.omega C sequence)
    (entries : ∀ n y, ZFSet.pair (natSetCode n) y ∈ sequence ↔ y = compressionStamp base n) :
    InjectionCode ZFSet.omega C sequence := by
  refine ⟨function, ?_⟩
  intro x y z first second
  obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode x).1 (ZFSet.pair_mem_prod.1 (function.1 first)).1
  obtain ⟨m, rfl⟩ := (mem_omega_iff_natSetCode y).1 (ZFSet.pair_mem_prod.1 (function.1 second)).1
  have equal := ((entries n z).1 first).symm.trans ((entries m z).1 second)
  have same : n = m := by
    by_contra different
    rcases Nat.lt_or_gt_of_ne different with lower | greater
    · have member := (compressionStamp_mem_iff base n m).2 lower
      rw [equal] at member
      exact ZFSet.mem_irrefl _ member
    · have member := (compressionStamp_mem_iff base m n).2 greater
      rw [equal] at member
      exact ZFSet.mem_irrefl _ member
  exact congrArg natSetCode same

namespace ExternalColumnCode
variable {C K base sequence cap : ZFSet.{u}} (code : ExternalColumnCode C K base sequence cap)
include code

theorem old_below {a : ZFSet.{u}} (ha : a ∈ K) (n : Nat) : a ∈ compressionStamp base n :=
  compressionStamp_old_mem (Or.inl (code.old_bound a ha)) n

end ExternalColumnCode

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_IntervalHeightFormulas
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

theorem truth_intervalHeightFormula {n} (L r D rD lo hi f : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (intervalHeightFormula L r D rD lo hi f) env ↔
      IntervalHeightCode (env L) (env r) (env D) (env rD) (env lo) (env hi) (env f) := by
  simp only [intervalHeightFormula, Truth, truth_functionFormula,
    truth_imp, truth_pairMembershipFormula]
  change (ZFSet.IsFunc (env L) (env D) (env f) ∧
    (∀ x ∈ env L, ∀ y ∈ env L, ∀ a ∈ env D, ∀ b ∈ env D,
      x ≠ y → ZFSet.pair x y ∈ env r → ZFSet.pair x a ∈ env f →
        ZFSet.pair y b ∈ env f → ZFSet.pair a b ∈ env rD) ∧
    (∀ x ∈ env L, ∀ a ∈ env D, ZFSet.pair x a ∈ env f →
      ZFSet.pair (env lo) a ∈ env rD ∧ ZFSet.pair a (env hi) ∈ env rD)) ↔ _
  constructor
  · rintro ⟨function, strict, inside⟩
    refine ⟨⟨function, ?_⟩, ?_⟩
    · intro x hx y hy different lower a b first second
      exact strict x hx y hy a (ZFSet.pair_mem_prod.1 (function.1 first)).2
        b (ZFSet.pair_mem_prod.1 (function.1 second)).2 different lower first second
    · intro x a entry
      have bounds := ZFSet.pair_mem_prod.1 (function.1 entry)
      exact inside x bounds.1 a bounds.2 entry
  · intro code
    refine ⟨code.function, ?_, ?_⟩
    · intro x hx y hy a _ b _ different lower first second
      exact code.strict x hx y hy different lower a b first second
    · intro x _ a _ entry
      exact code.inside x a entry

end PartitionPilot.Forcing.BoundedFormula

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_IndexedSubstructureCodes
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

theorem pair_mem_indexedSuborderGraph (I B R domains i v : ZFSet.{u}) :
    ZFSet.pair i v ∈ indexedSuborderGraph I B R domains ↔
      i ∈ I ∧ v ∈ R ∧ ∃ x ∈ relationFiber B domains i, ∃ y ∈ relationFiber B domains i,
        v = ZFSet.pair x y := by
  rw [indexedSuborderGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, j, hj, w, hw, x, hx, y, hy, equal, value, first, second⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hj, hw, x, (mem_relationFiber _ _ _ _).2 ⟨hx, first⟩,
      y, (mem_relationFiber _ _ _ _).2 ⟨hy, second⟩, value⟩
  · rintro ⟨hi, hv, x, hx, y, hy, equal⟩
    obtain ⟨hx, first⟩ := (mem_relationFiber _ _ _ _).1 hx
    obtain ⟨hy, second⟩ := (mem_relationFiber _ _ _ _).1 hy
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hi, hv⟩, i, hi, v, hv, x, hx, y, hy, rfl, equal, first, second⟩

theorem pair_mem_indexedSubmeetGraph (I B μ domains i v : ZFSet.{u}) :
    ZFSet.pair i v ∈ indexedSubmeetGraph I B μ domains ↔
      i ∈ I ∧ v ∈ μ ∧ ∃ x ∈ relationFiber B domains i, ∃ y ∈ relationFiber B domains i,
        ∃ w ∈ relationFiber B domains i, v = ZFSet.pair (ZFSet.pair x y) w := by
  rw [indexedSubmeetGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, j, hj, v', hv, x, hx, y, hy, w, hw, equal, value, first, second, third⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hj, hv, x, (mem_relationFiber _ _ _ _).2 ⟨hx, first⟩,
      y, (mem_relationFiber _ _ _ _).2 ⟨hy, second⟩,
      w, (mem_relationFiber _ _ _ _).2 ⟨hw, third⟩, value⟩
  · rintro ⟨hi, hv, x, hx, y, hy, w, hw, equal⟩
    obtain ⟨hx, first⟩ := (mem_relationFiber _ _ _ _).1 hx
    obtain ⟨hy, second⟩ := (mem_relationFiber _ _ _ _).1 hy
    obtain ⟨hw, third⟩ := (mem_relationFiber _ _ _ _).1 hw
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hi, hv⟩, i, hi, v, hv, x, hx, y, hy,
      w, hw, rfl, equal, first, second, third⟩

theorem suborderFiber_pair_iff {I B R domains i x y : ZFSet.{u}} (hi : i ∈ I) :
    ZFSet.pair x y ∈ relationFiber R (indexedSuborderGraph I B R domains) i ↔
      ZFSet.pair x y ∈ R ∧ x ∈ relationFiber B domains i ∧ y ∈ relationFiber B domains i := by
  rw [mem_relationFiber, pair_mem_indexedSuborderGraph]
  constructor
  · rintro ⟨hxy, _, _, a, ha, b, hb, equal⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hxy, ha, hb⟩
  · rintro ⟨hxy, hx, hy⟩
    exact ⟨hxy, hi, hxy, x, hx, y, hy, rfl⟩

theorem submeetFiber_triple_iff {I B μ domains i x y w : ZFSet.{u}} (hi : i ∈ I) :
    ZFSet.pair (ZFSet.pair x y) w ∈ relationFiber μ (indexedSubmeetGraph I B μ domains) i ↔
      ZFSet.pair (ZFSet.pair x y) w ∈ μ ∧ x ∈ relationFiber B domains i ∧
        y ∈ relationFiber B domains i ∧ w ∈ relationFiber B domains i := by
  rw [mem_relationFiber, pair_mem_indexedSubmeetGraph]
  constructor
  · rintro ⟨hxy, _, _, a, ha, b, hb, c, hc, equal⟩
    obtain ⟨ab, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 ab
    exact ⟨hxy, ha, hb, hc⟩
  · rintro ⟨hxy, hx, hy, hw⟩
    exact ⟨hxy, hi, hxy, x, hx, y, hy, w, hw, rfl⟩

namespace BoundedFormula

theorem truth_indexedSuborderEntryFormula {n} (z I B R domains : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (indexedSuborderEntryFormula z I B R domains) env ↔
      env z ∈ indexedSuborderGraph (env I) (env B) (env R) (env domains) := by
  simp only [indexedSuborderEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_pairMembershipFormula, indexedSuborderGraph, ZFSet.mem_sep]
  refine ⟨fun h => ⟨?_, h⟩, And.right⟩
  obtain ⟨i, hi, v, hv, _, _, _, _, equal, _⟩ := h
  change env z = ZFSet.pair i v at equal
  rw [equal]
  exact ZFSet.pair_mem_prod.2 ⟨hi, hv⟩

theorem truth_indexedSubmeetEntryFormula {n} (z I B μ domains : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (indexedSubmeetEntryFormula z I B μ domains) env ↔
      env z ∈ indexedSubmeetGraph (env I) (env B) (env μ) (env domains) := by
  simp only [indexedSubmeetEntryFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_orderedTripleFormula, truth_pairMembershipFormula, indexedSubmeetGraph, ZFSet.mem_sep]
  refine ⟨fun h => ⟨?_, h⟩, And.right⟩
  obtain ⟨i, hi, v, hv, _, _, _, _, _, _, equal, _⟩ := h
  change env z = ZFSet.pair i v at equal
  rw [equal]
  exact ZFSet.pair_mem_prod.2 ⟨hi, hv⟩
end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundIndexedSubstructures
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
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable {I B R domains : ZFSet.{u}} (hI : I ∈ M.sets) (hB : B ∈ M.sets)
variable (hR : R ∈ M.sets) (hDomains : domains ∈ M.sets)
include pairing unions powers separation hI hB hR hDomains

theorem indexedSuborderGraph_mem : indexedSuborderGraph I B R domains ∈ M.sets := by
  let params := extend I (extend B (extend R (extend domains Fin.elim0)))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.indexedSuborderEntryFormula 0 1 2 3 4) params
    (Fin.cases hI (Fin.cases hB (Fin.cases hR (Fin.cases hDomains (fun j => Fin.elim0 j)))))
    (M.prod_mem pairing unions powers separation hI hR)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.indexedSuborderEntryFormula 0 1 2 3 4) (extend z params))
      (ZFSet.prod I R) = indexedSuborderGraph I B R domains := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_indexedSuborderEntryFormula]
    exact ⟨And.right, fun hz => ⟨(ZFSet.mem_sep.1 hz).1, hz⟩⟩
  exact equal ▸ selected

theorem indexedSubmeetGraph_mem : indexedSubmeetGraph I B R domains ∈ M.sets := by
  let params := extend I (extend B (extend R (extend domains Fin.elim0)))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.indexedSubmeetEntryFormula 0 1 2 3 4) params
    (Fin.cases hI (Fin.cases hB (Fin.cases hR (Fin.cases hDomains (fun j => Fin.elim0 j)))))
    (M.prod_mem pairing unions powers separation hI hR)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.indexedSubmeetEntryFormula 0 1 2 3 4) (extend z params))
      (ZFSet.prod I R) = indexedSubmeetGraph I B R domains := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_indexedSubmeetEntryFormula]
    exact ⟨And.right, fun hz => ⟨(ZFSet.mem_sep.1 hz).1, hz⟩⟩
  exact equal ▸ selected

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundExternalLocalHeightSelection
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing
universe u
namespace BoundedFormula
open SetFormula

theorem truth_intervalHeightCandidateFormula {n}
    (Ps rs D rD lo hi i f boundPs boundRs : Fin n) (env : Fin n → ZFSet.{u})
    (sourceBound : env boundPs = ⋃₀ ⋃₀ env Ps)
    (orderBound : env boundRs = ⋃₀ ⋃₀ env rs) :
    Truth (intervalHeightCandidateFormula Ps rs D rD lo hi i f boundPs boundRs) env ↔
      intervalHeightCandidate (env Ps) (env rs) (env D) (env rD)
        (env lo) (env hi) (env i) (env f) := by
  simp only [intervalHeightCandidateFormula, truth_exMem, Truth,
    truth_pairMembershipFormula, truth_intervalHeightFormula]
  change (∃ P ∈ env boundPs, ∃ r ∈ env boundRs,
    ZFSet.pair (env i) P ∈ env Ps ∧ ZFSet.pair (env i) r ∈ env rs ∧
      IntervalHeightCode P r (env D) (env rD) (env lo) (env hi) (env f)) ↔ _
  rw [sourceBound, orderBound]
  rfl

theorem truth_intervalHeightRelationEntryFormula {n}
    (z I W Ps rs D rD lo hi boundPs boundRs : Fin n) (env : Fin n → ZFSet.{u})
    (sourceBound : env boundPs = ⋃₀ ⋃₀ env Ps)
    (orderBound : env boundRs = ⋃₀ ⋃₀ env rs) :
    Truth (intervalHeightRelationEntryFormula z I W Ps rs D rD lo hi boundPs boundRs) env ↔
      ∃ i ∈ env I, ∃ f ∈ env W, env z = ZFSet.pair i f ∧
        intervalHeightCandidate (env Ps) (env rs) (env D) (env rD) (env lo) (env hi) i f := by
  simp only [intervalHeightRelationEntryFormula, truth_exMem, Truth, truth_orderedPairFormula]
  apply exists_congr
  intro i
  apply and_congr_right
  intro _
  apply exists_congr
  intro f
  apply and_congr_right
  intro _
  exact and_congr Iff.rfl (truth_intervalHeightCandidateFormula Ps.succ.succ rs.succ.succ
    D.succ.succ rD.succ.succ lo.succ.succ hi.succ.succ 1 0 boundPs.succ.succ boundRs.succ.succ
    (extend f (extend i env)) sourceBound orderBound)

end BoundedFormula

namespace TransitiveGround
open SetFormula

theorem intervalHeightRelation_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I W Ps rs D rD lo hi : ZFSet.{u}}
    (hI : I ∈ M.sets) (hW : W ∈ M.sets) (hPs : Ps ∈ M.sets) (hrs : rs ∈ M.sets)
    (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) (hlo : lo ∈ M.sets) (hhi : hi ∈ M.sets) :
    intervalHeightRelation I W Ps rs D rD lo hi ∈ M.sets := by
  have sourceBound := M.union_mem unions (M.union_mem unions hPs)
  have orderBound := M.union_mem unions (M.union_mem unions hrs)
  let params := extend I (extend W (extend Ps (extend rs (extend D (extend rD
    (extend lo (extend hi (extend (⋃₀ ⋃₀ Ps) (extend (⋃₀ ⋃₀ rs) Fin.elim0)))))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.intervalHeightRelationEntryFormula 0 1 2 3 4 5 6 7 8 9 10) params
    (Fin.cases hI (Fin.cases hW (Fin.cases hPs (Fin.cases hrs (Fin.cases hD
      (Fin.cases hrD (Fin.cases hlo (Fin.cases hhi (Fin.cases sourceBound
        (Fin.cases orderBound (fun j => Fin.elim0 j)))))))))))
    (M.prod_mem pairing unions powers separation hI hW)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.intervalHeightRelationEntryFormula 0 1 2 3 4 5 6 7 8 9 10)
      (extend z params)) (ZFSet.prod I W) = intervalHeightRelation I W Ps rs D rD lo hi := by
    apply ZFSet.ext
    intro z
    rw [intervalHeightRelation, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl
      (BoundedFormula.truth_intervalHeightRelationEntryFormula 0 1 2 3 4 5 6 7 8 9 10
        (extend z params) rfl rfl)
  exact equal ▸ selected

end TransitiveGround
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u

theorem exists_intervalHeight_family (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {I B Ps rs D rD c lo hi : ZFSet.{u}}
    (sources : FunctionGraphOn I Ps) (orders : FunctionGraphOn I rs)
    (sourceBound : ∀ i, sources.value i ⊆ B)
    (hI : I ∈ M.sets) (hB : B ∈ M.sets) (hPs : Ps ∈ M.sets) (hrs : rs ∈ M.sets)
    (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) (hc : c ∈ M.sets)
    (hlo : lo ∈ M.sets) (hhi : hi ∈ M.sets) (hOmega : ZFSet.omega ∈ M.sets)
    (injection : InjectionCode D ZFSet.omega c)
    (witnesses : ∀ i, ∃ f ∈ M.sets, IntervalHeightCode (sources.value i) (orders.value i) D rD lo hi f) :
    ∃ family ∈ M.sets, ZFSet.IsFunc I (M.groundRelations B D) family ∧
      ∀ (i : {i : ZFSet.{u} // i ∈ I}) f, ZFSet.pair i.val f ∈ family →
        f ∈ M.sets ∧ IntervalHeightCode (sources.value i) (orders.value i) D rD lo hi f ∧
        relationImage (sources.value i) D f ∈ M.sets ∧
        M.groundEmbeddable (relationImage (sources.value i) D f) ZFSet.omega := by
  let W := M.groundRelations B D
  have hW : W ∈ M.sets := M.groundRelations_mem pairing unions powers separation hB hD
  have hRelation := M.intervalHeightRelation_mem pairing unions powers separation
    hI hW hPs hrs hD hrD hlo hhi
  have total : ∀ i ∈ I, ∃ f ∈ W,
      ZFSet.pair i f ∈ intervalHeightRelation I W Ps rs D rD lo hi := by
    intro i memI
    let j : {i : ZFSet.{u} // i ∈ I} := ⟨i, memI⟩
    obtain ⟨f, ground, code⟩ := witnesses j
    have bound : f ⊆ ZFSet.prod B D := by
      intro z hz
      obtain ⟨x, hx, a, ha, rfl⟩ := ZFSet.mem_prod.1 (code.function.1 hz)
      exact ZFSet.pair_mem_prod.2 ⟨sourceBound j hx, ha⟩
    have fW : f ∈ W := (M.mem_groundRelations B D f).2 ⟨ground, bound⟩
    exact ⟨f, fW, (pair_mem_intervalHeightRelation I W Ps rs D rD lo hi i f).2
      ⟨memI, fW, (intervalHeightCandidate_iff sources orders j f).2 code⟩⟩
  obtain ⟨family, ground, function, selected⟩ := M.uniformize_relation
    pairing unions powers separation choice hI hW hRelation total
  refine ⟨family, ground, function, ?_⟩
  intro i f entry
  have candidate := (pair_mem_intervalHeightRelation I W Ps rs D rD lo hi i.val f).1 (selected entry)
  have fGround := ((M.mem_groundRelations B D f).1 candidate.2.1).1
  have code := (intervalHeightCandidate_iff sources orders i f).1 candidate.2.2
  have rangeGround := M.relationImage_mem separation (sources.value_mem M hPs i) hD fGround
  exact ⟨fGround, code, rangeGround, M.groundEmbeddable_restrict separation rangeGround hOmega
    (fun _ hz => ((mem_relationImage _ _ _ _).1 hz).1) ⟨c, hc, injection⟩⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace GroundCompressionCompletion
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)
variable (P r μ A : ZFSet.{u})
local notation "Q" => completion.externalPointCarrier P r μ A

theorem localTileCarrier_subset (request : ZFSet.{u}) : completion.localTileCarrier P r μ A request ⊆ Q :=
  fun _ hz => (mem_relationFiber _ _ _ _).1 hz |>.1

end GroundCompressionCompletion

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
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
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
local notation "Requests" => externalRequestCarrier I P0 (externalRectangles P0 G r0 μ0 A0)
include data group oldAction pairing unions powers separation infinite hG hP0

theorem localTileCarriers_spec :
    completion.localTileCarriers P0 r0 μ0 A0 ∈ M.sets ∧
      FunctionGraphOn Requests (completion.localTileCarriers P0 r0 μ0 A0) ∧
      ∀ i f, ZFSet.pair i f ∈ completion.localTileCarriers P0 r0 μ0 A0 ↔
        i ∈ Requests ∧ f = completion.localTileCarrier P0 r0 μ0 A0 i := by
  have ground := data.localTileGroundInputs group oldAction pairing unions powers separation infinite hG hP0
  exact ⟨M.relationFiberFamily_mem pairing unions powers separation data.words.requests_ground ground.1 ground.2.2.2.2,
    ⟨_, M.relationFiberFamily_function separation data.words.requests_ground ground.1 ground.2.2.2.2⟩,
    M.relationFiberFamily_entries separation data.words.requests_ground ground.1 ground.2.2.2.2⟩

theorem localTileOrders_spec :
    completion.localTileOrders P0 r0 μ0 A0 ∈ M.sets ∧
      FunctionGraphOn Requests (completion.localTileOrders P0 r0 μ0 A0) ∧
      ∀ i f, ZFSet.pair i f ∈ completion.localTileOrders P0 r0 μ0 A0 ↔
        i ∈ Requests ∧ f = completion.localTileOrder P0 r0 μ0 A0 i := by
  have ground := data.localTileGroundInputs group oldAction pairing unions powers separation infinite hG hP0
  have indexed := M.indexedSuborderGraph_mem pairing unions powers separation data.words.requests_ground
    ground.1 ground.2.1 ground.2.2.2.2
  exact ⟨M.relationFiberFamily_mem pairing unions powers separation data.words.requests_ground ground.2.1 indexed,
    ⟨_, M.relationFiberFamily_function separation data.words.requests_ground ground.2.1 indexed⟩,
    M.relationFiberFamily_entries separation data.words.requests_ground ground.2.1 indexed⟩

theorem localTileMeets_spec :
    completion.localTileMeets P0 r0 μ0 A0 ∈ M.sets ∧
      FunctionGraphOn Requests (completion.localTileMeets P0 r0 μ0 A0) ∧
      ∀ i f, ZFSet.pair i f ∈ completion.localTileMeets P0 r0 μ0 A0 ↔
        i ∈ Requests ∧ f = completion.localTileMeet P0 r0 μ0 A0 i := by
  have ground := data.localTileGroundInputs group oldAction pairing unions powers separation infinite hG hP0
  have indexed := M.indexedSubmeetGraph_mem pairing unions powers separation data.words.requests_ground
    ground.1 ground.2.2.1 ground.2.2.2.2
  exact ⟨M.relationFiberFamily_mem pairing unions powers separation data.words.requests_ground ground.2.2.1 indexed,
    ⟨_, M.relationFiberFamily_function separation data.words.requests_ground ground.2.2.1 indexed⟩,
    M.relationFiberFamily_entries separation data.words.requests_ground ground.2.2.1 indexed⟩

end GroundExternalGeometryInputs

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundExternalGeometryInputs
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 D rD c lo hi : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
local notation "Requests" => externalRequestCarrier I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "Q" => completion.externalPointCarrier P0 r0 μ0 A0
include data group oldAction pairing unions powers separation infinite choice hG hP0

theorem localHeightFamily_of_witnesses
    (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) (hc : c ∈ M.sets)
    (hlo : lo ∈ M.sets) (hhi : hi ∈ M.sets) (injection : InjectionCode D ZFSet.omega c)
    (witnesses : ∀ i ∈ Requests, ∃ h ∈ M.sets,
      IntervalHeightCode (completion.localTileCarrier P0 r0 μ0 A0 i)
        (completion.localTileOrder P0 r0 μ0 A0 i) D rD lo hi h) :
    Nonempty (GroundExternalLocalHeightData M initial I Sources Reps G m one T τ
      P0 r0 μ0 A0 D rD lo hi completion) := by
  have carriers := data.localTileCarriers_spec group oldAction pairing unions powers separation infinite hG hP0
  have orders := data.localTileOrders_spec group oldAction pairing unions powers separation infinite hG hP0
  have ground := data.localTileGroundInputs group oldAction pairing unions powers separation infinite hG hP0
  have carrierValue (i : {i : ZFSet.{u} // i ∈ Requests}) :
      carriers.2.1.value i = completion.localTileCarrier P0 r0 μ0 A0 i.val :=
    ((carriers.2.2 _ _).1 (carriers.2.1.value_entry i)).2
  have orderValue (i : {i : ZFSet.{u} // i ∈ Requests}) :
      orders.2.1.value i = completion.localTileOrder P0 r0 μ0 A0 i.val :=
    ((orders.2.2 _ _).1 (orders.2.1.value_entry i)).2
  have bound (i : {i : ZFSet.{u} // i ∈ Requests}) : carriers.2.1.value i ⊆ Q := by
    rw [carrierValue]
    exact completion.localTileCarrier_subset P0 r0 μ0 A0 i.val
  have localExists (i : {i : ZFSet.{u} // i ∈ Requests}) :
      ∃ h ∈ M.sets, IntervalHeightCode (carriers.2.1.value i) (orders.2.1.value i) D rD lo hi h := by
    rw [carrierValue, orderValue]
    exact witnesses i.val i.property
  obtain ⟨family, member, function, values⟩ := M.exists_intervalHeight_family
    pairing unions powers separation choice carriers.2.1 orders.2.1 bound data.words.requests_ground ground.1
    carriers.1 orders.1 hD hrD hc hlo hhi (M.omega_mem separation infinite) injection localExists
  refine ⟨⟨family, member, function, ?_⟩⟩
  intro i h entry
  have hi := (ZFSet.pair_mem_prod.1 (function.1 entry)).1
  have value := values ⟨i, hi⟩ h entry
  rw [carrierValue, orderValue] at value
  exact value

end PartitionPilot.Forcing.GroundExternalGeometryInputs

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundExternalLocalHeightFamilies
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI




namespace PartitionPilot.Forcing.GroundExternalGeometryInputs
open SetRealization SetFormula Compression Compression.RecursiveMaps.CosetGeometry
universe u
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
local notation "p" => data.localTilePresentation group oldAction pairing unions powers separation infinite hG
local notation "Index" => ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "requestPresentation" => externalRequestPresentation I P0 (externalRectangles P0 G r0 μ0 A0)
include data group oldAction pairing unions powers separation infinite hG

theorem localTileOrder_iff :
    letI := group.toGroup
    ∀ (r : Index) (x y : ((family).tile r).Space),
      ZFSet.pair ((p r).encode x) ((p r).encode y) ∈
        completion.localTileOrder P0 r0 μ0 A0 (externalRequestIndexCode r) ↔
          ((family).tile r).order.le x y := by
  let := group.toGroup
  intro r x y
  have hx := (p r).encode_mem x
  have hy := (p r).encode_mem y
  have hi : externalRequestIndexCode r ∈ externalRequestCarrier I P0 (externalRectangles P0 G r0 μ0 A0) :=
    (requestPresentation).encode_mem r
  rw [GroundCompressionCompletion.localTileOrder, suborderFiber_pair_iff hi]
  change (_ ∧ (p r).encode x ∈ (p r).carrier ∧ (p r).encode y ∈ (p r).carrier) ↔ _
  simp only [hx, hy, and_true]
  exact ((data.externalGeometry_entries group oldAction pairing unions powers separation infinite hG).1 _ _).trans
    (((family).placedTile (action) 1 r).le_iff x y)

theorem localTileMeet_iff :
    letI := group.toGroup
    ∀ (r : Index) (x y z : ((family).tile r).Space),
      ZFSet.pair (ZFSet.pair ((p r).encode x) ((p r).encode y)) ((p r).encode z) ∈
        completion.localTileMeet P0 r0 μ0 A0 (externalRequestIndexCode r) ↔
          ((family).tile r).order.meet x y = z := by
  let := group.toGroup
  intro r x y z
  have hx := (p r).encode_mem x
  have hy := (p r).encode_mem y
  have hz := (p r).encode_mem z
  have hi : externalRequestIndexCode r ∈ externalRequestCarrier I P0 (externalRectangles P0 G r0 μ0 A0) :=
    (requestPresentation).encode_mem r
  rw [GroundCompressionCompletion.localTileMeet, submeetFiber_triple_iff hi]
  change (_ ∧ (p r).encode x ∈ (p r).carrier ∧ (p r).encode y ∈ (p r).carrier ∧
    (p r).encode z ∈ (p r).carrier) ↔ _
  simp only [hx, hy, hz, and_true]
  refine ((data.externalGeometry_entries group oldAction pairing unions powers separation infinite hG).2.1 _ _ _).trans ?_
  rw [← ((family).placedTile (action) 1 r).map_meet]
  exact ⟨fun equal => embedding_injective ((family).placedTile (action) 1 r).toMeetEmbedding equal,
    fun equal => congrArg _ equal⟩

omit data group oldAction pairing unions powers separation infinite hG in
theorem localTileOrder_shape (r : Index) :
    completion.localTileOrder P0 r0 μ0 A0 (externalRequestIndexCode r) ⊆
      ZFSet.prod (completion.localTileCarrier P0 r0 μ0 A0 (externalRequestIndexCode r))
        (completion.localTileCarrier P0 r0 μ0 A0 (externalRequestIndexCode r)) := by
  intro z hz
  have entry := (mem_relationFiber _ _ _ _).1 hz |>.2
  obtain ⟨_, _, x, hx, y, hy, rfl⟩ := (pair_mem_indexedSuborderGraph _ _ _ _ _ _).1 entry
  exact ZFSet.pair_mem_prod.2 ⟨hx, hy⟩

theorem localTileMeet_eq_canonical (r : Index) :
    completion.localTileMeet P0 r0 μ0 A0 (externalRequestIndexCode r) =
      canonicalMeetGraph (completion.localTileCarrier P0 r0 μ0 A0 (externalRequestIndexCode r))
        (completion.localTileOrder P0 r0 μ0 A0 (externalRequestIndexCode r)) := by
  let := group.toGroup
  have related := data.localTileOrder_iff group oldAction pairing unions powers separation infinite hG r
  have meet := data.localTileMeet_iff group oldAction pairing unions powers separation infinite hG r
  apply ZFSet.ext
  intro v
  constructor
  · intro hv
    have entry := (mem_relationFiber _ _ _ _).1 hv |>.2
    obtain ⟨_, _, x, hx, y, hy, z, hz, rfl⟩ := (pair_mem_indexedSubmeetGraph _ _ _ _ _ _).1 entry
    obtain ⟨x, rfl⟩ := ((p r).mem_carrier x).1 hx
    obtain ⟨y, rfl⟩ := ((p r).mem_carrier y).1 hy
    obtain ⟨z, rfl⟩ := ((p r).mem_carrier z).1 hz
    exact ((p r).canonicalMeetGraph_iff ((family).tile r).order related x y z).2 ((meet x y z).1 hv)
  · intro hv
    obtain ⟨x, hx, y, hy, z, hz, rfl, _⟩ := (mem_canonicalMeetGraph _ _ _).1 hv
    obtain ⟨x, rfl⟩ := ((p r).mem_carrier x).1 hx
    obtain ⟨y, rfl⟩ := ((p r).mem_carrier y).1 hy
    obtain ⟨z, rfl⟩ := ((p r).mem_carrier z).1 hz
    exact (meet x y z).2 (((p r).canonicalMeetGraph_iff ((family).tile r).order related x y z).1 hv)

theorem localTileMeet_code (r : Index) :
    MeetOrderCode (completion.localTileCarrier P0 r0 μ0 A0 (externalRequestIndexCode r))
      (completion.localTileOrder P0 r0 μ0 A0 (externalRequestIndexCode r))
      (completion.localTileMeet P0 r0 μ0 A0 (externalRequestIndexCode r)) := by
  let := group.toGroup
  rw [data.localTileMeet_eq_canonical group oldAction pairing unions powers separation infinite hG]
  exact (p r).canonicalMeetOrderCode ((family).tile r).order
    (localTileOrder_shape (completion := completion) r)
    (data.localTileOrder_iff group oldAction pairing unions powers separation infinite hG r)

end PartitionPilot.Forcing.GroundExternalGeometryInputs




namespace PartitionPilot.Forcing.GroundExternalGeometryInputs
open SetRealization SetFormula Compression Compression.RecursiveMaps.CosetGeometry
universe u
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
local notation "q" => data.externalPointPresentation group oldAction pairing unions powers separation infinite hG
local notation "p" => data.localTilePresentation group oldAction pairing unions powers separation infinite hG
local notation "Index" => ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "U" => completion.algebra.union.fields 0
local notation "Q" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "vcode" => completion.externalFamilyVertexCode group oldAction data.original
local notation "vertexGraph(" r "," i ")" => indexedRelationSection U Q (completion.localTileVertexImages P0 r0 μ0 A0)
  (ZFSet.pair (externalRequestIndexCode r) (vcode r i))
include data group oldAction pairing unions powers separation infinite hG

theorem localTileVertexGraph_iff :
    letI := group.toGroup
    ∀ (r : Index) (i : Option ((family).Child r)) (x : SetMembers U) (y : ((family).tile r).Space),
      ZFSet.pair (SetMembers.raw x) ((p r).encode y) ∈ vertexGraph(r, i) ↔
        ((family).flatVertex r i).toFun x = y := by
  let := group.toGroup
  intro r i x y
  have qc := data.externalPointPresentation_carrier group oldAction pairing unions powers separation infinite hG
  rw [pair_mem_indexedRelationSection]
  have hy : (p r).encode y ∈ Q := qc ▸ (q).encode_mem _
  simp only [SetMembers.raw_mem, hy, true_and]
  change ZFSet.pair
    ((completion.externalFamilyTileVertexPresentation group oldAction data.original).encode ⟨r, i, x⟩)
    ((q).encode (((family).placedTile (action) 1 r).toFun y)) ∈ _ ↔ _
  rw [data.localTileVertexImages_entry_iff group oldAction pairing unions powers separation infinite hG]
  rw [← (family).flatVertex_copy]
  exact ⟨fun equal => embedding_injective ((family).placedTile (action) 1 r).toMeetEmbedding equal,
    fun equal => congrArg _ equal⟩

theorem localTileVertexGraph_eq :
    letI := group.toGroup
    ∀ (r : Index) (i : Option ((family).Child r)),
      vertexGraph(r, i) = (SetMembers.presentation U).graph (p r) ((family).flatVertex r i).toFun := by
  let := group.toGroup
  intro r i
  have qc := data.externalPointPresentation_carrier group oldAction pairing unions powers separation infinite hG
  apply ZFSet.ext
  intro v
  constructor
  · intro hv
    obtain ⟨x, hx, y, hy, rfl, entry⟩ := (mem_indexedRelationSection _ _ _ _ _).1 hv
    obtain ⟨y, rfl⟩ := ((q).mem_carrier y).1 (qc.symm ▸ hy)
    let x' := SetMembers.ofMem x hx
    have copied := (data.localTileVertexImages_entry_iff group oldAction pairing unions powers separation infinite hG
      r i x' y).1 (by simpa only [GroundCompressionCompletion.externalFamilyTileVertexPresentation_encode,
        x', SetMembers.raw_ofMem] using entry)
    have equal : (q).encode y = (p r).encode (((family).flatVertex r i).toFun x') := by
      change (q).encode y = (q).encode (((family).placedTile (action) 1 r).toFun _)
      rw [(family).flatVertex_copy, copied]
    rw [equal]
    exact ((SetMembers.presentation U).mem_graph (p r) _ _).2
      ⟨x', by change ZFSet.pair (SetMembers.raw x') _ = _; simp only [x', SetMembers.raw_ofMem]⟩
  · intro hv
    obtain ⟨x, rfl⟩ := ((SetMembers.presentation U).mem_graph (p r) _ _).1 hv
    exact (data.localTileVertexGraph_iff group oldAction pairing unions powers separation infinite hG r i x _).2 rfl

theorem localTileVertexGraph_mem (hP0 : P0 ∈ M.sets) (r : Index) (i : Option ((family).Child r)) :
    vertexGraph(r, i) ∈ M.sets := by
  have grounds := data.localTileGroundInputs group oldAction pairing unions powers separation infinite hG hP0
  have requestGround := M.transitive data.words.requests_ground
    ((externalRequestPresentation I P0 (externalRectangles P0 G r0 μ0 A0)).encode_mem r)
  have indexGround := M.transitive (M.natSetCode_mem separation infinite 3)
    (data.localTileVertexCode_mem group oldAction r i)
  exact M.indexedRelationSection_mem pairing unions powers separation (completion.algebra.union.ground 0)
    grounds.1 grounds.2.2.2.1 (M.orderedPair_mem pairing requestGround indexGround)

end PartitionPilot.Forcing.GroundExternalGeometryInputs




namespace PartitionPilot.Forcing.GroundExternalGeometryInputs
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 C Q rQ original D rD c lo hi : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
variable (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
variable (heights : GroundCompressionHeightData M initial I Sources Reps G m one T
  completion.algebra.union P0 C Q rQ original)
variable (columns : ordinalSetProperty C) (heightOrder : StrictLinearOrderCode Q rQ)
variable (hC : C ∈ M.sets) (hQ : Q ∈ M.sets) (hrQ : rQ ∈ M.sets)
variable (target : DenseOrderCode D rD) (injection : InjectionCode D ZFSet.omega c)
variable (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) (hc : c ∈ M.sets)
variable (hlo : lo ∈ D) (hhi : hi ∈ D) (gap : ZFSet.pair lo hi ∈ rD)
local notation "Requests" => externalRequestCarrier I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "U" => completion.algebra.union.fields 0
local notation "family" => completion.externalFamily group oldAction data.original
include data group oldAction pairing unions powers separation collection infinite hG hP0
  heights columns heightOrder hC hQ hrQ target injection hD hrD hc hlo hhi gap

theorem exists_localTileHeight (i : ZFSet.{u}) (hIndex : i ∈ Requests) :
    ∃ height ∈ M.sets,
      IntervalHeightCode (completion.localTileCarrier P0 r0 μ0 A0 i)
        (completion.localTileOrder P0 r0 μ0 A0 i) D rD lo hi height := by
  let := group.toGroup
  let requests := externalRequestPresentation I P0 (externalRectangles P0 G r0 μ0 A0)
  obtain ⟨r, rfl⟩ := (requests.mem_carrier i).1 hIndex
  let p := data.localTilePresentation group oldAction pairing unions powers separation infinite hG r
  let source := SetMembers.presentation U
  let values := SetMembers.presentation (ZFSet.prod C Q)
  let linear := lexHeightOrder_code columns heightOrder
  let seed := heights.code.strictHeightGraph.smallHeight completion.algebra.union.meet linear
  have seedGround : source.graph values seed.value ∈ M.sets := by
    rw [StrictHeightGraphCode.smallHeight_graph]
    exact heights.height_ground
  have seedSmall : M.groundEmbeddable (relationImage U (ZFSet.prod C Q)
      (source.graph values seed.value)) ZFSet.omega := by
    rw [StrictHeightGraphCode.smallHeight_graph]
    exact heights.range_countable
  have carriers := data.localTileCarriers_spec group oldAction pairing unions powers separation infinite hG hP0
  have meets := data.localTileMeets_spec group oldAction pairing unions powers separation infinite hG hP0
  have indexMember := requests.encode_mem r
  have carrierGround : p.carrier ∈ M.sets :=
    M.pair_right (M.transitive carriers.1 ((carriers.2.2 _ _).2 ⟨indexMember, rfl⟩))
  have meetGround : completion.localTileMeet P0 r0 μ0 A0 (externalRequestIndexCode r) ∈ M.sets :=
    M.pair_right (M.transitive meets.1 ((meets.2.2 _ _).2 ⟨indexMember, rfl⟩))
  have tileMeet := data.localTileMeet_code group oldAction pairing unions powers separation infinite hG r
  have rootGround : source.graph p (((family).tile r).root.toFun) ∈ M.sets := by
    change source.graph p (((family).flatVertex r none).toFun) ∈ M.sets
    rw [← data.localTileVertexGraph_eq group oldAction pairing unions powers separation infinite hG]
    exact data.localTileVertexGraph_mem group oldAction pairing unions powers separation infinite hG hP0 r none
  have childrenGround : ∀ j, source.graph p ((((family).tile r).child j).toFun) ∈ M.sets := by
    intro j
    change source.graph p (((family).flatVertex r (some j)).toFun) ∈ M.sets
    rw [← data.localTileVertexGraph_eq group oldAction pairing unions powers separation infinite hG]
    exact data.localTileVertexGraph_mem group oldAction pairing unions powers separation infinite hG hP0 r (some j)
  obtain ⟨height, ground, code, _, _⟩ := M.exists_requestTileIntervalHeight
    pairing unions powers separation collection infinite source values
    ((family).top) ((family).greatest) linear.smallOrder seed
    (fun _ _ => Iff.rfl) linear target injection (completion.algebra.union.ground 0)
    (M.prod_mem pairing unions powers separation hC hQ) seedGround
    (M.lexHeightOrder_mem pairing unions powers separation hC hQ hrQ)
    hD hrD hc seedSmall hlo hhi gap ((family).request r) p carrierGround meetGround
    (data.localTileOrder_iff group oldAction pairing unions powers separation infinite hG r)
    tileMeet.operation
    (fun x y => (data.localTileMeet_iff group oldAction pairing unions powers separation infinite hG r x y _).2 rfl)
    rootGround childrenGround
  exact ⟨height, ground, code⟩

theorem exists_localHeightFamily (choice : Realize M.sets SetFormula.choice Fin.elim0) :
    Nonempty (GroundExternalLocalHeightData M initial I Sources Reps G m one T τ
      P0 r0 μ0 A0 D rD lo hi completion) := by
  apply data.localHeightFamily_of_witnesses group oldAction pairing unions powers separation infinite choice hG hP0
    hD hrD hc (M.transitive hD hlo) (M.transitive hD hhi) injection
  exact data.exists_localTileHeight group oldAction pairing unions powers separation collection infinite hG hP0
    heights columns heightOrder hC hQ hrQ target injection hD hrD hc hlo hhi gap

end PartitionPilot.Forcing.GroundExternalGeometryInputs

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundExternalTileSlotSupports
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
universe u

theorem pair_mem_transportedTileCoordinates (V E I B D action heights v x q : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair v x) q ∈ transportedTileCoordinates V E I B D action heights ↔
      v ∈ V ∧ x ∈ B ∧ q ∈ D ∧ ∃ w ∈ E, ∃ i ∈ I, ∃ y ∈ B, ∃ h ∈ ZFSet.sUnion (ZFSet.sUnion heights),
        v = ZFSet.pair (natSetCode 1) (ZFSet.pair w i) ∧ ZFSet.pair i h ∈ heights ∧
        ZFSet.pair (ZFSet.pair w y) x ∈ action ∧ ZFSet.pair y q ∈ h := by
  rw [transportedTileCoordinates, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, v', hv, w, hw, i, hi, x', hx, q', hq, y, hy, h, hh, equal, body⟩
    obtain ⟨left, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 left
    exact ⟨hv, hx, hq, w, hw, i, hi, y, hy, h, hh, body⟩
  · rintro ⟨hv, hx, hq, w, hw, i, hi, y, hy, h, hh, body⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hv, hx⟩, hq⟩,
      v, hv, w, hw, i, hi, x, hx, q, hq, y, hy, h, hh, rfl, body⟩

theorem transportedTileCoordinates_partial {V E I B D action heights : ZFSet.{u}}
    (family : FunctionGraphOn I heights)
    (localUnique : ∀ i h y a b, ZFSet.pair i h ∈ heights →
      ZFSet.pair y a ∈ h → ZFSet.pair y b ∈ h → a = b)
    (actionInjective : ∀ w ∈ E, ∀ y ∈ B, ∀ z ∈ B, ∀ x,
      ZFSet.pair (ZFSet.pair w y) x ∈ action →
      ZFSet.pair (ZFSet.pair w z) x ∈ action → y = z) :
    PartialFunctionCode (ZFSet.prod V B) D (transportedTileCoordinates V E I B D action heights) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro p a b first second
  have hp := (ZFSet.pair_mem_prod.1 (ZFSet.mem_sep.1 first).1).1
  obtain ⟨v, _, x, _, rfl⟩ := ZFSet.mem_prod.1 hp
  obtain ⟨_, _, _, w, hw, i, hi, y, hy, h, _, shape, field, acting, value⟩ :=
    (pair_mem_transportedTileCoordinates _ _ _ _ _ _ _ _ _ _).1 first
  obtain ⟨_, _, _, w', _, i', _, y', hy', h', _, shape', field', acting', value'⟩ :=
    (pair_mem_transportedTileCoordinates _ _ _ _ _ _ _ _ _ _).1 second
  have wi := ZFSet.pair_inj.1 ((ZFSet.pair_inj.1 (shape.symm.trans shape')).2)
  obtain ⟨rfl, rfl⟩ := wi
  have sameH : h = h' := (family.value_eq_of_entry ⟨i, hi⟩ field).symm.trans
    (family.value_eq_of_entry ⟨i, hi⟩ field')
  subst h'
  have sameY := actionInjective w hw y hy y' hy' x acting acting'
  subst y'
  exact localUnique i h y a b field value value'

theorem pair_mem_externalOwnerHeightGraph (P B V C D old owner depths columns coordinates x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ externalOwnerHeightGraph P B V C D old owner depths columns coordinates ↔
      ZFSet.pair x y ∈ old ∨ (x ∈ B ∧ x ∉ P ∧ ∃ v ∈ V, ∃ n ∈ ZFSet.omega, ∃ a ∈ C, ∃ q ∈ D,
        y = ZFSet.pair a q ∧ ZFSet.pair x v ∈ owner ∧ ZFSet.pair v n ∈ depths ∧
          ZFSet.pair n a ∈ columns ∧ ZFSet.pair (ZFSet.pair v x) q ∈ coordinates) := by
  rw [externalOwnerHeightGraph, ZFSet.mem_union]
  apply or_congr Iff.rfl
  rw [ZFSet.mem_sep]
  constructor
  · rintro ⟨_, x', hx, v, hv, n, hn, a, ha, q, hq, equal, fresh, body⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hx, fresh, v, hv, n, hn, a, ha, q, hq, rfl, body⟩
  · rintro ⟨hx, fresh, v, hv, n, hn, a, ha, q, hq, rfl, body⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hx, ZFSet.pair_mem_prod.2 ⟨ha, hq⟩⟩,
      x, hx, v, hv, n, hn, a, ha, q, hq, rfl, fresh, body⟩

theorem externalOwnerHeightGraph_old {P B V C D old owner depths columns coordinates x y : ZFSet.{u}}
    (hx : x ∈ P) :
    ZFSet.pair x y ∈ externalOwnerHeightGraph P B V C D old owner depths columns coordinates ↔
      ZFSet.pair x y ∈ old := by
  rw [pair_mem_externalOwnerHeightGraph]
  exact ⟨fun h => h.elim id (fun h => False.elim (h.2.1 hx)), Or.inl⟩

theorem externalOwnerHeightGraph_function {P B V C D old owner depths columns coordinates : ZFSet.{u}}
    (subset : P ⊆ B) (oldFunction : ZFSet.IsFunc P (ZFSet.prod C D) old)
    (ownerFunction : ZFSet.IsFunc B V owner) (depthFunction : ZFSet.IsFunc V ZFSet.omega depths)
    (columnFunction : ZFSet.IsFunc ZFSet.omega C columns)
    (coordinatePartial : PartialFunctionCode (ZFSet.prod V B) D coordinates)
    (coordinateTotal : ∀ x ∈ B, x ∉ P → ∀ v, ZFSet.pair x v ∈ owner →
      ∃ q ∈ D, ZFSet.pair (ZFSet.pair v x) q ∈ coordinates) :
    ZFSet.IsFunc B (ZFSet.prod C D) (externalOwnerHeightGraph P B V C D old owner depths columns coordinates) := by
  have oldUnique := functionCode_partial oldFunction
  have ownerUnique := functionCode_partial ownerFunction
  have depthUnique := functionCode_partial depthFunction
  have columnUnique := functionCode_partial columnFunction
  refine ⟨?_, ?_⟩
  · intro z hz
    rcases (ZFSet.mem_union.1 hz) with oldEntry | freshEntry
    · obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (oldFunction.1 oldEntry)
      exact ZFSet.pair_mem_prod.2 ⟨subset hx, hy⟩
    · exact (ZFSet.mem_sep.1 freshEntry).1
  · intro x hx
    by_cases oldX : x ∈ P
    · obtain ⟨y, entry, unique⟩ := oldFunction.2 x oldX
      exact ⟨y, (externalOwnerHeightGraph_old oldX).2 entry,
        fun z hz => unique z ((externalOwnerHeightGraph_old oldX).1 hz)⟩
    · obtain ⟨v, owned, _⟩ := ownerFunction.2 x hx
      have hv := (ZFSet.pair_mem_prod.1 (ownerFunction.1 owned)).2
      obtain ⟨n, atDepth, _⟩ := depthFunction.2 v hv
      have hn := (ZFSet.pair_mem_prod.1 (depthFunction.1 atDepth)).2
      obtain ⟨a, atColumn, _⟩ := columnFunction.2 n hn
      have ha := (ZFSet.pair_mem_prod.1 (columnFunction.1 atColumn)).2
      obtain ⟨q, hq, coord⟩ := coordinateTotal x hx oldX v owned
      refine ⟨ZFSet.pair a q, (pair_mem_externalOwnerHeightGraph _ _ _ _ _ _ _ _ _ _ _ _).2
        (Or.inr ⟨hx, oldX, v, hv, n, hn, a, ha, q, hq, rfl, owned, atDepth, atColumn, coord⟩), ?_⟩
      intro y entry
      rcases (pair_mem_externalOwnerHeightGraph _ _ _ _ _ _ _ _ _ _ _ _).1 entry with oldEntry | fresh
      · exact False.elim (oldX (ZFSet.pair_mem_prod.1 (oldFunction.1 oldEntry)).1)
      · obtain ⟨_, _, v', _, n', _, a', _, q', _, rfl, owned', depth', column', coord'⟩ := fresh
        have sameV := ownerUnique.unique x v' v owned' owned
        subst v'
        have sameN := depthUnique.unique v n' n depth' atDepth
        subst n'
        have sameA := columnUnique.unique n a' a column' atColumn
        have sameQ := coordinatePartial.unique (ZFSet.pair v x) q' q coord' coord
        exact congrArg₂ ZFSet.pair sameA sameQ

end

section
open SetFormula
universe u
namespace BoundedFormula

theorem truth_transportedTileCoordinateFormula {n} (z V E I B D action heights bound one : Fin n)
    (env : Fin n → ZFSet.{u}) (boundEq : env bound = ZFSet.sUnion (ZFSet.sUnion (env heights)))
    (oneEq : env one = natSetCode 1) :
    Truth (transportedTileCoordinateFormula z V E I B D action heights bound one) env ↔
      env z ∈ transportedTileCoordinates (env V) (env E) (env I) (env B) (env D) (env action) (env heights) := by
  simp only [transportedTileCoordinateFormula, truth_exMem, Truth, truth_orderedTripleFormula,
    truth_orderedRightTripleFormula, truth_pairMembershipFormula, truth_tripleMembershipFormula]
  simp only [extend, Fin.cases_zero, Fin.cases_succ]
  rw [boundEq, oneEq, transportedTileCoordinates, ZFSet.mem_sep]
  refine ⟨fun h => ⟨?_, h⟩, And.right⟩
  obtain ⟨v, hv, _, _, _, _, x, hx, q, hq, _, _, _, _, equal, _⟩ := h
  rw [equal]
  exact ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hv, hx⟩, hq⟩

theorem truth_ownerHeightFreshFormula {n} (z P B V C D owner depths columns coordinates omega : Fin n)
    (env : Fin n → ZFSet.{u}) (omegaEq : env omega = ZFSet.omega) :
    Truth (ownerHeightFreshFormula z P B V C D owner depths columns coordinates omega) env ↔
      ∃ x ∈ env B, ∃ v ∈ env V, ∃ n ∈ ZFSet.omega, ∃ a ∈ env C, ∃ q ∈ env D,
        env z = ZFSet.pair x (ZFSet.pair a q) ∧ x ∉ env P ∧ ZFSet.pair x v ∈ env owner ∧
          ZFSet.pair v n ∈ env depths ∧ ZFSet.pair n a ∈ env columns ∧
          ZFSet.pair (ZFSet.pair v x) q ∈ env coordinates := by
  simp only [ownerHeightFreshFormula, truth_exMem, Truth, truth_orderedRightTripleFormula,
    truth_pairMembershipFormula, truth_tripleMembershipFormula]
  simp only [extend, Fin.cases_zero, Fin.cases_succ]
  rw [omegaEq]
  rfl

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem transportedTileCoordinates_mem {V E I B D action heights : ZFSet.{u}}
    (hV : V ∈ M.sets) (hE : E ∈ M.sets) (hI : I ∈ M.sets) (hB : B ∈ M.sets)
    (hD : D ∈ M.sets) (hAction : action ∈ M.sets) (hHeights : heights ∈ M.sets) :
    transportedTileCoordinates V E I B D action heights ∈ M.sets := by
  have hBound := M.union_mem unions (M.union_mem unions hHeights)
  have hZero := M.empty_mem ⟨B, hB⟩
  have hOne : natSetCode 1 ∈ M.sets := M.insert_mem pairing unions hZero hZero
  let params := extend V (extend E (extend I (extend B (extend D (extend action
    (extend heights (extend (ZFSet.sUnion (ZFSet.sUnion heights)) (extend (natSetCode 1) Fin.elim0))))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.transportedTileCoordinateFormula 0 1 2 3 4 5 6 7 8 9) params
    (Fin.cases hV (Fin.cases hE (Fin.cases hI (Fin.cases hB (Fin.cases hD
      (Fin.cases hAction (Fin.cases hHeights (Fin.cases hBound (Fin.cases hOne (fun i => Fin.elim0 i))))))))))
    (M.prod_mem pairing unions powers separation (M.prod_mem pairing unions powers separation hV hB) hD)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.transportedTileCoordinateFormula 0 1 2 3 4 5 6 7 8 9) (extend z params))
      (ZFSet.prod (ZFSet.prod V B) D) = transportedTileCoordinates V E I B D action heights := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_transportedTileCoordinateFormula _ _ _ _ _ _ _ _ _ _ _ rfl rfl]
    exact ⟨And.right, fun h => ⟨(ZFSet.mem_sep.1 h).1, h⟩⟩
  exact equal ▸ selected

theorem externalOwnerHeightGraph_mem {P B V C D old owner depths columns coordinates : ZFSet.{u}}
    (hP : P ∈ M.sets) (hB : B ∈ M.sets) (hV : V ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets)
    (hOld : old ∈ M.sets) (hOwner : owner ∈ M.sets) (hDepths : depths ∈ M.sets)
    (hColumns : columns ∈ M.sets) (hCoordinates : coordinates ∈ M.sets) (hOmega : ZFSet.omega ∈ M.sets) :
    externalOwnerHeightGraph P B V C D old owner depths columns coordinates ∈ M.sets := by
  let params := extend P (extend B (extend V (extend C (extend D (extend owner (extend depths
    (extend columns (extend coordinates (extend ZFSet.omega Fin.elim0)))))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.ownerHeightFreshFormula 0 1 2 3 4 5 6 7 8 9 10) params
    (Fin.cases hP (Fin.cases hB (Fin.cases hV (Fin.cases hC (Fin.cases hD (Fin.cases hOwner
      (Fin.cases hDepths (Fin.cases hColumns (Fin.cases hCoordinates (Fin.cases hOmega (fun i => Fin.elim0 i)))))))))))
    (M.prod_mem pairing unions powers separation hB (M.prod_mem pairing unions powers separation hC hD))
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.ownerHeightFreshFormula 0 1 2 3 4 5 6 7 8 9 10) (extend z params))
      (ZFSet.prod B (ZFSet.prod C D)) =
      ZFSet.sep (fun z => ∃ x ∈ B, ∃ v ∈ V, ∃ n ∈ ZFSet.omega, ∃ a ∈ C, ∃ q ∈ D,
        z = ZFSet.pair x (ZFSet.pair a q) ∧ x ∉ P ∧ ZFSet.pair x v ∈ owner ∧
          ZFSet.pair v n ∈ depths ∧ ZFSet.pair n a ∈ columns ∧
          ZFSet.pair (ZFSet.pair v x) q ∈ coordinates) (ZFSet.prod B (ZFSet.prod C D)) := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_ownerHeightFreshFormula _ _ _ _ _ _ _ _ _ _ _ _ rfl)
  exact M.binary_union_mem pairing unions hOld (equal ▸ selected)

end TransitiveGround
end

section
universe u

theorem externalOwnerHeightGraph_range_subset {P B V C D old owner depths columns coordinates : ZFSet.{u}}
    (oldFunction : ZFSet.IsFunc P (ZFSet.prod C D) old) :
    relationImage B (ZFSet.prod C D) (externalOwnerHeightGraph P B V C D old owner depths columns coordinates) ⊆
      relationImage P (ZFSet.prod C D) old ∪ ZFSet.prod (relationImage ZFSet.omega C columns) D := by
  intro y hy
  obtain ⟨hy, x, _, entry⟩ := (mem_relationImage _ _ _ _).1 hy
  rcases (pair_mem_externalOwnerHeightGraph _ _ _ _ _ _ _ _ _ _ _ _).1 entry with retained | fresh
  · exact ZFSet.mem_union.2 (Or.inl ((mem_relationImage _ _ _ _).2
      ⟨hy, x, (ZFSet.pair_mem_prod.1 (oldFunction.1 retained)).1, retained⟩))
  · obtain ⟨_, _, _, _, n, hn, a, ha, q, hq, rfl, _, _, column, _⟩ := fresh
    exact ZFSet.mem_union.2 (Or.inr (ZFSet.pair_mem_prod.2
      ⟨(mem_relationImage _ _ _ _).2 ⟨ha, n, hn, column⟩, hq⟩))

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})

theorem externalOwnerHeightGraph_range_small
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {P B V C D old owner depths columns coordinates : ZFSet.{u}}
    (hP : P ∈ M.sets) (hB : B ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets)
    (hOld : old ∈ M.sets) (hColumns : columns ∈ M.sets)
    (hHeight : externalOwnerHeightGraph P B V C D old owner depths columns coordinates ∈ M.sets)
    (oldFunction : ZFSet.IsFunc P (ZFSet.prod C D) old)
    (oldSmall : M.groundEmbeddable (relationImage P (ZFSet.prod C D) old) ZFSet.omega)
    (columnSmall : M.groundEmbeddable (relationImage ZFSet.omega C columns) ZFSet.omega)
    (coordinateSmall : M.groundEmbeddable D ZFSet.omega) :
    relationImage B (ZFSet.prod C D) (externalOwnerHeightGraph P B V C D old owner depths columns coordinates) ∈ M.sets ∧
      M.groundEmbeddable (relationImage B (ZFSet.prod C D)
        (externalOwnerHeightGraph P B V C D old owner depths columns coordinates)) ZFSet.omega := by
  have omega := M.omega_mem separation infinite
  have rangeGround := M.relationImage_mem separation hB (M.prod_mem pairing unions powers separation hC hD) hHeight
  have oldGround := M.relationImage_mem separation hP (M.prod_mem pairing unions powers separation hC hD) hOld
  have columnsGround := M.relationImage_mem separation omega hC hColumns
  have productGround := M.prod_mem pairing unions powers separation columnsGround hD
  have productSmall := M.groundEmbeddable_product pairing unions powers separation infinite columnsGround hD columnSmall coordinateSmall
  have totalSmall := M.groundCountable_binary_union pairing unions powers separation infinite choice
    oldGround productGround oldSmall productSmall
  exact ⟨rangeGround, M.groundEmbeddable_restrict separation rangeGround omega
    (externalOwnerHeightGraph_range_subset oldFunction) totalSmall⟩

end TransitiveGround

end

section
universe u

theorem externalOwnerHeightGraph_fresh {P B V C D old owner depths columns coordinates x a q : ZFSet.{u}}
    (oldFunction : ZFSet.IsFunc P (ZFSet.prod C D) old) (fresh : x ∉ P) :
    ZFSet.pair x (ZFSet.pair a q) ∈ externalOwnerHeightGraph P B V C D old owner depths columns coordinates ↔
      x ∈ B ∧ a ∈ C ∧ q ∈ D ∧ ∃ v ∈ V, ∃ n ∈ ZFSet.omega,
        ZFSet.pair x v ∈ owner ∧ ZFSet.pair v n ∈ depths ∧ ZFSet.pair n a ∈ columns ∧
          ZFSet.pair (ZFSet.pair v x) q ∈ coordinates := by
  rw [pair_mem_externalOwnerHeightGraph]
  constructor
  · intro entry
    rcases entry with retained | new
    · exact False.elim (fresh (ZFSet.pair_mem_prod.1 (oldFunction.1 retained)).1)
    · obtain ⟨hx, _, v, hv, n, hn, a', ha, q', hq, equal, body⟩ := new
      obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
      exact ⟨hx, ha, hq, v, hv, n, hn, body⟩
  · rintro ⟨hx, ha, hq, v, hv, n, hn, body⟩
    exact Or.inr ⟨hx, fresh, v, hv, n, hn, a, ha, q, hq, rfl, body⟩

theorem ExternalColumnCode.entries_increasing {C K base columns cap n m a b : ZFSet.{u}}
    (code : ExternalColumnCode C K base columns cap)
    (hn : n ∈ ZFSet.omega) (hm : m ∈ ZFSet.omega) (before : n ∈ m)
    (first : ZFSet.pair n a ∈ columns) (second : ZFSet.pair m b ∈ columns) : a ∈ b := by
  obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
  obtain ⟨m, rfl⟩ := (mem_omega_iff_natSetCode m).1 hm
  rw [(code.entries n a).1 first, (code.entries m b).1 second]
  exact (compressionStamp_mem_iff base n m).2 ((natSetCode_mem_iff n m).1 before)

theorem externalOwnerHeightGraph_strictLex {P B V C D r old owner depths columns coordinates base cap rD : ZFSet.{u}}
    (subset : P ⊆ B) (seed : StrictLexHeightCode P C D r old rD)
    (ownerFunction : ZFSet.IsFunc B V owner) (depthFunction : ZFSet.IsFunc V ZFSet.omega depths)
    (columnCode : ExternalColumnCode C (heightColumns P C D old) base columns cap)
    (coordinatePartial : PartialFunctionCode (ZFSet.prod V B) D coordinates)
    (coordinateTotal : ∀ x ∈ B, x ∉ P → ∀ v, ZFSet.pair x v ∈ owner →
      ∃ q ∈ D, ZFSet.pair (ZFSet.pair v x) q ∈ coordinates)
    (noFreshBelowOld : ∀ x ∈ B, x ∉ P → ∀ y ∈ P, ZFSet.pair x y ∉ r)
    (depthMonotone : ∀ x ∈ B, x ∉ P → ∀ y ∈ B, y ∉ P → ∀ v w n m,
      ZFSet.pair x v ∈ owner → ZFSet.pair y w ∈ owner → ZFSet.pair v n ∈ depths →
      ZFSet.pair w m ∈ depths → ZFSet.pair x y ∈ r → n = m ∨ n ∈ m)
    (sameDepthOwner : ∀ x ∈ B, x ∉ P → ∀ y ∈ B, y ∉ P → ∀ v w n,
      ZFSet.pair x v ∈ owner → ZFSet.pair y w ∈ owner → ZFSet.pair v n ∈ depths →
      ZFSet.pair w n ∈ depths → ZFSet.pair x y ∈ r → v = w)
    (coordinateStrict : ∀ v x y a b, ZFSet.pair x y ∈ r → x ≠ y →
      ZFSet.pair (ZFSet.pair v x) a ∈ coordinates →
      ZFSet.pair (ZFSet.pair v y) b ∈ coordinates → ZFSet.pair a b ∈ rD) :
    StrictLexHeightCode B C D r
      (externalOwnerHeightGraph P B V C D old owner depths columns coordinates) rD := by
  refine ⟨externalOwnerHeightGraph_function subset seed.function ownerFunction depthFunction
    columnCode.function coordinatePartial coordinateTotal, ?_⟩
  intro x hx y hy a q b s lower different first second
  by_cases oldX : x ∈ P
  · have oldFirst := (externalOwnerHeightGraph_old oldX).1 first
    by_cases oldY : y ∈ P
    · exact seed.strict x oldX y oldY a q b s lower different oldFirst
        ((externalOwnerHeightGraph_old oldY).1 second)
    · obtain ⟨_, _, _, _, _, n, hn, _, _, column, _⟩ :=
        (externalOwnerHeightGraph_fresh seed.function oldY).1 second
      obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
      refine Or.inl ?_
      rw [(columnCode.entries n b).1 column]
      exact columnCode.old_below (mem_heightColumns_of_entry seed.function oldFirst) n
  · have oldY : y ∉ P := fun hyP => noFreshBelowOld x hx oldX y hyP lower
    obtain ⟨_, _, _, v, _, n, hn, ownedX, depthX, colX, coordX⟩ :=
      (externalOwnerHeightGraph_fresh seed.function oldX).1 first
    obtain ⟨_, _, _, w, _, m, hm, ownedY, depthY, colY, coordY⟩ :=
      (externalOwnerHeightGraph_fresh seed.function oldY).1 second
    rcases depthMonotone x hx oldX y hy oldY v w n m ownedX ownedY depthX depthY lower with same | before
    · subst m
      have sameOwner := sameDepthOwner x hx oldX y hy oldY v w n ownedX ownedY depthX depthY lower
      subst w
      exact Or.inr ⟨(functionCode_partial columnCode.function).unique n a b colX colY,
        coordinateStrict v x y q s lower different coordX coordY⟩
    · exact Or.inl (columnCode.entries_increasing hn hm before colX colY)

end

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_ExternalTileCoordinateRealization
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.GroundExternalGeometryInputs
open SetRealization SetFormula Compression Compression.RecursiveMaps.CosetGeometry
universe u
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
local notation "Requests" => externalRequestCarrier I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "Index" => ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "Q" => completion.externalPointCarrier P0 r0 μ0 A0
variable {D rD lo hi : ZFSet.{u}}
variable (heights : GroundExternalLocalHeightData M initial I Sources Reps G m one T τ P0 r0 μ0 A0 D rD lo hi completion)
local notation "coordinates" => heights.coordinates
local notation "localp" => data.localTilePresentation group oldAction pairing unions powers separation infinite hG
include data group oldAction pairing unions powers separation infinite hG

theorem externalTileCoordinates_iff :
    letI := group.toGroup
    ∀ (w : External (SetMembers G) (family).Letters) (r : Index) (a : ((family).tile r).Space)
      (h : ZFSet.{u}), ZFSet.pair (externalRequestIndexCode r) h ∈ heights.family → ∀ d,
      ZFSet.pair (ZFSet.pair ((vpres).encode (.inr (w, r)))
        ((q).encode (((family).placedTile (action) w r).toFun a))) d ∈ coordinates ↔
          ZFSet.pair (((localp r)).encode a) d ∈ h := by
  let := group.toGroup
  intro w r a h selected d
  have sc := completion.externalFamilyGroupPresentation_carrier group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground
  have qc := data.externalPointPresentation_carrier group oldAction pairing unions powers separation infinite hG
  have vc := (data.externalStarPresentations_carriers group oldAction pairing unions powers separation infinite hG).1
  have acted := (data.externalGeometry_entries group oldAction pairing unions powers separation infinite hG).2.2.1
  have code := (heights.values _ _ selected).2.1
  rw [GroundExternalLocalHeightData.coordinates, pair_mem_transportedTileCoordinates]
  constructor
  · rintro ⟨_, _, _, w', _, r', _, y, _, h', _, equal, selected', acted', value⟩
    change ZFSet.pair (natSetCode 1) (ZFSet.pair ((s).encode w) (externalRequestIndexCode r)) =
      ZFSet.pair (natSetCode 1) (ZFSet.pair w' r') at equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 (ZFSet.pair_inj.1 equal).2
    have sameH := (show FunctionGraphOn Requests heights.family from ⟨_, heights.function⟩).unique selected' selected
    subst h'
    have hy := (ZFSet.pair_mem_prod.1 (code.function.1 value)).1
    obtain ⟨b, rfl⟩ := (data.localTileCarrier_image group oldAction pairing unions powers separation infinite hG r y).1 hy
    have same := (acted w (((family).placedTile (action) 1 r).toFun b)
      (((family).placedTile (action) w r).toFun a)).1 acted'
    rw [(family).translate_tile, mul_one] at same
    have ba := embedding_injective ((family).placedTile (action) w r).toMeetEmbedding same
    subst b
    exact value
  · intro value
    have hd := (ZFSet.pair_mem_prod.1 (code.function.1 value)).2
    refine ⟨vc ▸ (vpres).encode_mem _, qc ▸ (q).encode_mem _, hd,
      (s).encode w, sc ▸ (s).encode_mem _, externalRequestIndexCode r,
      (externalRequestPresentation I P0 (externalRectangles P0 G r0 μ0 A0)).encode_mem _,
      ((localp r)).encode a, ?_, h, pair_second_mem_doubleUnion selected, rfl, selected, ?_, value⟩
    · exact completion.localTileCarrier_subset P0 r0 μ0 A0 _ (((localp r)).encode_mem a)
    · apply (acted w (((family).placedTile (action) 1 r).toFun a) _).2
      rw [(family).translate_tile, mul_one]

include heights in
theorem externalTileCoordinates_ground (hP0 : P0 ∈ M.sets) (hD : D ∈ M.sets) : coordinates ∈ M.sets := by
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  exact M.transportedTileCoordinates_mem pairing unions powers separation
    (data.externalStarCarriers_ground pairing unions powers separation hG).1 data.group.carrier_mem
    data.words.requests_ground geometry.carrier_ground hD geometry.action_ground heights.family_ground

include heights in
theorem externalTileCoordinates_partial (hP0 : P0 ∈ M.sets) :
    PartialFunctionCode (ZFSet.prod
      (M.externalStarVertices G (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)) Requests m one) Q) D coordinates := by
  let := group.toGroup
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  have sc := completion.externalFamilyGroupPresentation_carrier group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground
  have qc := data.externalPointPresentation_carrier group oldAction pairing unions powers separation infinite hG
  have acted := (data.externalGeometry_entries group oldAction pairing unions powers separation infinite hG).2.2.1
  apply transportedTileCoordinates_partial (show FunctionGraphOn Requests heights.family from ⟨_, heights.function⟩)
  · intro i h y a b selected first second
    exact (functionCode_partial (heights.values _ _ selected).2.1.function).unique y a b first second
  · intro w hw y hy z hz x first second
    obtain ⟨w, rfl⟩ := ((s).mem_carrier w).1 (sc.symm ▸ hw)
    obtain ⟨y, rfl⟩ := ((q).mem_carrier y).1 (qc.symm ▸ hy)
    obtain ⟨z, rfl⟩ := ((q).mem_carrier z).1 (qc.symm ▸ hz)
    have hx := (ZFSet.pair_mem_prod.1 (geometry.action.function.1 first)).2
    obtain ⟨x, rfl⟩ := ((q).mem_carrier x).1 (qc.symm ▸ hx)
    have same := ((acted w y x).1 first).trans ((acted w z x).1 second).symm
    apply congrArg (q).encode
    have back := congrArg ((family).translate (action) w⁻¹) same
    simpa only [(family).translate_left_inverse] using back

theorem externalTileCoordinates_total :
    letI := group.toGroup
    ∀ (w : External (SetMembers G) (family).Letters) (r : Index) (a : ((family).tile r).Space),
      ∃ d ∈ D, ZFSet.pair (ZFSet.pair ((vpres).encode (.inr (w, r)))
        ((q).encode (((family).placedTile (action) w r).toFun a))) d ∈ coordinates := by
  let := group.toGroup
  intro w r a
  obtain ⟨h, selected, _⟩ := heights.function.2 _
    ((externalRequestPresentation I P0 (externalRectangles P0 G r0 μ0 A0)).encode_mem r)
  have code := (heights.values _ _ selected).2.1
  obtain ⟨d, value, _⟩ := code.function.2 _ (((localp r)).encode_mem a)
  exact ⟨d, (ZFSet.pair_mem_prod.1 (code.function.1 value)).2,
    (data.externalTileCoordinates_iff group oldAction pairing unions powers separation infinite hG heights w r a h selected d).2 value⟩

theorem externalTileCoordinates_strict :
    letI := group.toGroup
    ∀ (w : External (SetMembers G) (family).Letters) (r : Index) (a b : ((family).tile r).Space),
      a ≠ b → ((family).tile r).order.le a b → ∀ d e,
      ZFSet.pair (ZFSet.pair ((vpres).encode (.inr (w, r)))
        ((q).encode (((family).placedTile (action) w r).toFun a))) d ∈ coordinates →
      ZFSet.pair (ZFSet.pair ((vpres).encode (.inr (w, r)))
        ((q).encode (((family).placedTile (action) w r).toFun b))) e ∈ coordinates →
      ZFSet.pair d e ∈ rD := by
  let := group.toGroup
  intro w r a b distinct lower d e first second
  obtain ⟨h, selected, _⟩ := heights.function.2 _
    ((externalRequestPresentation I P0 (externalRectangles P0 G r0 μ0 A0)).encode_mem r)
  have code := (heights.values _ _ selected).2.1
  have first' := (data.externalTileCoordinates_iff group oldAction pairing unions powers separation infinite hG heights w r a h selected d).1 first
  have second' := (data.externalTileCoordinates_iff group oldAction pairing unions powers separation infinite hG heights w r b h selected e).1 second
  exact code.strict _ (((localp r)).encode_mem a) _ (((localp r)).encode_mem b)
    (fun equal => distinct (((localp r)).injective equal))
    ((data.localTileOrder_iff group oldAction pairing unions powers separation infinite hG r a b).2 lower) d e first' second'

end PartitionPilot.Forcing.GroundExternalGeometryInputs

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_ExternalOwnerCoordinateLaws
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetRealization SetFormula Compression.RecursiveMaps.CosetGeometry
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
local notation "U" => completion.algebra.union.fields 0
local notation "P" => completion.externalSeedCarrier P0 r0 μ0 A0

include data group oldAction pairing unions powers separation infinite hG in
theorem externalSeedHeights_spec (hP0 : P0 ∈ M.sets) {C D rD original : ZFSet.{u}}
    (heights : GroundCompressionHeightData M initial I Sources Reps G m one T completion.algebra.union P0 C D rD original)
    (hC : C ∈ M.sets) (hD : D ∈ M.sets) :
    P ∈ M.sets ∧ completion.externalSeedHeight P0 r0 μ0 A0 C D heights.height ∈ M.sets ∧
      StrictLexHeightCode P C D (completion.externalPointOrder P0 r0 μ0 A0)
        (completion.externalSeedHeight P0 r0 μ0 A0 C D heights.height) rD ∧
      relationImage P (ZFSet.prod C D) (completion.externalSeedHeight P0 r0 μ0 A0 C D heights.height) =
        relationImage U (ZFSet.prod C D) heights.height ∧
      M.groundEmbeddable (relationImage P (ZFSet.prod C D)
        (completion.externalSeedHeight P0 r0 μ0 A0 C D heights.height)) ZFSet.omega := by
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  have copyGround := geometry.copies_ground _ data.group.group_code.identity_mem
  have copy := data.externalIdentityCopy_ideal group oldAction pairing unions powers separation infinite hG
  have range := pushedHeightGraph_range copy.injection heights.code.function
  refine ⟨M.relationImage_mem separation (completion.algebra.union.ground 0) geometry.carrier_ground copyGround,
    M.pushedHeightGraph_mem pairing unions powers separation (completion.algebra.union.ground 0)
      geometry.carrier_ground (M.prod_mem pairing unions powers separation hC hD) copyGround heights.height_ground,
    pushedHeightGraph_strictLex copy heights.code, range, ?_⟩
  exact range.symm ▸ heights.range_countable

end GroundExternalGeometryInputs



end PartitionPilot.Forcing




namespace PartitionPilot.Forcing.GroundExternalGeometryInputs
open SetRealization SetFormula Compression.RecursiveMaps.CosetGeometry
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets)
local notation "Q" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "seedCarrier" => completion.externalSeedCarrier P0 r0 μ0 A0

include data group oldAction pairing unions powers separation infinite hG

theorem externalSeedCarrier_no_new_below {x y : ZFSet.{u}} (hx : x ∈ Q)
    (fresh : x ∉ seedCarrier) (old : y ∈ seedCarrier) :
    ZFSet.pair x y ∉ completion.externalPointOrder P0 r0 μ0 A0 :=
  fun lower => fresh (data.externalSeedCarrier_lower group oldAction pairing unions powers separation infinite hG hx old lower)

end PartitionPilot.Forcing.GroundExternalGeometryInputs




namespace PartitionPilot.Forcing.GroundExternalGeometryInputs
open SetRealization SetFormula Compression Compression.RecursiveMaps.CosetGeometry
universe u
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
local notation "Q" => completion.externalPointCarrier P0 r0 μ0 A0
variable {D rD lo hi : ZFSet.{u}}
variable (heights : GroundExternalLocalHeightData M initial I Sources Reps G m one T τ P0 r0 μ0 A0 D rD lo hi completion)
local notation "coordinates" => heights.coordinates
include data group oldAction pairing unions powers separation infinite hG

theorem externalTileCoordinates_support :
    letI := group.toGroup
    ∀ v x d, ZFSet.pair (ZFSet.pair v x) d ∈ coordinates →
      ∃ (w : External (SetMembers G) (family).Letters) (r : Index) (a : ((family).tile r).Space),
        v = (vpres).encode (.inr (w, r)) ∧ x = (q).encode (((family).placedTile (action) w r).toFun a) := by
  let := group.toGroup
  intro v x d entry
  have sc := completion.externalFamilyGroupPresentation_carrier group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground
  have qc := data.externalPointPresentation_carrier group oldAction pairing unions powers separation infinite hG
  have acted := (data.externalGeometry_entries group oldAction pairing unions powers separation infinite hG).2.2.1
  obtain ⟨_, hx, _, w, hw, r, hr, y, _, h, _, equal, selected, acting, value⟩ :=
    (pair_mem_transportedTileCoordinates _ _ _ _ _ _ _ _ _ _).1 entry
  obtain ⟨w, rfl⟩ := ((s).mem_carrier w).1 (sc.symm ▸ hw)
  obtain ⟨r, rfl⟩ := ((externalRequestPresentation I P0 (externalRectangles P0 G r0 μ0 A0)).mem_carrier r).1 hr
  have code := (heights.values _ _ selected).2.1
  have localMember := (ZFSet.pair_mem_prod.1 (code.function.1 value)).1
  obtain ⟨a, rfl⟩ := (data.localTileCarrier_image group oldAction pairing unions powers separation infinite hG r y).1 localMember
  obtain ⟨x, rfl⟩ := ((q).mem_carrier x).1 (qc.symm ▸ hx)
  have translated := (acted w (((family).placedTile (action) 1 r).toFun a) x).1 acting
  rw [(family).translate_tile, mul_one] at translated
  exact ⟨w, r, a, equal, congrArg (q).encode translated.symm⟩

include heights in
theorem externalTileCoordinates_owner_total :
    ∀ x ∈ Q, x ∉ completion.externalSeedCarrier P0 r0 μ0 A0 → ∀ v,
      ZFSet.pair x v ∈ completion.externalStarOwner P0 r0 μ0 A0 →
      ∃ d ∈ D, ZFSet.pair (ZFSet.pair v x) d ∈ coordinates := by
  let := group.toGroup
  intro x _ fresh v owner
  obtain ⟨w, r, a, rfl, rfl, _⟩ :=
    data.externalStarOwner_fresh_tile group oldAction pairing unions powers separation infinite hG x v owner fresh
  exact data.externalTileCoordinates_total group oldAction pairing unions powers separation infinite hG heights w r a

include heights in
theorem externalTileCoordinates_raw_strict :
    ∀ v x y a b, ZFSet.pair x y ∈ completion.externalPointOrder P0 r0 μ0 A0 → x ≠ y →
      ZFSet.pair (ZFSet.pair v x) a ∈ coordinates →
      ZFSet.pair (ZFSet.pair v y) b ∈ coordinates → ZFSet.pair a b ∈ rD := by
  let := group.toGroup
  intro v x y a b lower distinct first second
  obtain ⟨w, r, x', rfl, rfl⟩ :=
    data.externalTileCoordinates_support group oldAction pairing unions powers separation infinite hG heights v x a first
  obtain ⟨w', r', y', sameVertex, samePoint⟩ :=
    data.externalTileCoordinates_support group oldAction pairing unions powers separation infinite hG heights _ y b second
  have same := Sum.inr.inj ((vpres).injective sameVertex)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  subst y
  have localLower := (((family).placedTile (action) w r).le_iff x' y').1
    (((data.externalGeometry_entries group oldAction pairing unions powers separation infinite hG).1 _ _).1 lower)
  have localDistinct : x' ≠ y' := fun equal => distinct (congrArg
    (fun z => (q).encode (((family).placedTile (action) w r).toFun z)) equal)
  exact data.externalTileCoordinates_strict group oldAction pairing unions powers separation infinite hG
    heights w r x' y' localDistinct localLower a b first second

end PartitionPilot.Forcing.GroundExternalGeometryInputs



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
open SetFormula
universe u

theorem pushedBirthGraph_oldMeet {A B T rA rB μA μB e old : ZFSet.{u}}
    (source : MeetOrderCode A rA μA) (target : MeetOrderCode B rB μB)
    (embedding : MeetEmbeddingCode A B rA rB μA μB e)
    (born : ZFSet.IsFunc A T old) (oldMeet : OldMeetCode rA μA old) :
    OldMeetCode rB μB (pushedHeightGraph A B T e old) := by
  intro x y z a b c bornY bornX earlier notLower meetXY bornZ
  have function := pushedHeightGraph_function embedding.injection born
  have hx := (ZFSet.pair_mem_prod.1 (function.1 bornX)).1
  have hy := (ZFSet.pair_mem_prod.1 (function.1 bornY)).1
  obtain ⟨_, x0, hx0, copyX⟩ := (mem_relationImage _ _ _ _).1 hx
  obtain ⟨_, y0, hy0, copyY⟩ := (mem_relationImage _ _ _ _).1 hy
  obtain ⟨z0, sourceMeet, _⟩ := source.operation.2 (ZFSet.pair x0 y0) (ZFSet.pair_mem_prod.2 ⟨hx0, hy0⟩)
  have hz0 := (ZFSet.pair_mem_prod.1 (source.operation.1 sourceMeet)).2
  obtain ⟨z1, copyZ, _⟩ := embedding.injection.function.2 z0 hz0
  have targetMeet := embedding.map_meet x0 y0 z0 x y z1 sourceMeet copyX copyY copyZ
  obtain ⟨_, _, unique⟩ := target.operation.2 (ZFSet.pair x y)
    (ZFSet.pair_mem_prod.1 (target.operation.1 meetXY)).1
  have equal := (unique z1 targetMeet).trans (unique z meetXY).symm
  subst z1
  exact oldMeet x0 y0 z0 a b c
    ((pushedHeightGraph_entry embedding.injection born copyY).1 bornY)
    ((pushedHeightGraph_entry embedding.injection born copyX).1 bornX) earlier
    (fun lower => notLower (embedding.monotone x0 y0 x y lower copyX copyY)) sourceMeet
    ((pushedHeightGraph_entry embedding.injection born copyZ).1 bornZ)

end PartitionPilot.Forcing


section

namespace PartitionPilot.Forcing.GroundExternalGeometryInputs
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 times birth : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets)
local notation "old" => completion.externalSeedBirth P0 r0 μ0 A0 times birth
local notation "P" => completion.externalSeedCarrier P0 r0 μ0 A0
include data group oldAction pairing unions powers separation infinite hG

theorem externalSeedBirth_spec (hP0 : P0 ∈ M.sets) (hTimes : times ∈ M.sets) (hBirth : birth ∈ M.sets)
    (born : ZFSet.IsFunc (completion.algebra.union.fields 0) times birth)
    (oldMeet : OldMeetCode (completion.algebra.union.fields 1) (completion.algebra.union.fields 2) birth) :
    old ∈ M.sets ∧ ZFSet.IsFunc P times old ∧
      OldMeetCode (completion.externalPointOrder P0 r0 μ0 A0) (completion.externalPointMeet P0 r0 μ0 A0) old := by
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  have embedding := data.externalIdentityCopy_ideal group oldAction pairing unions powers separation infinite hG
  exact ⟨M.pushedHeightGraph_mem pairing unions powers separation (completion.algebra.union.ground 0)
    geometry.carrier_ground hTimes (geometry.copies_ground _ data.group.group_code.identity_mem) hBirth,
    pushedHeightGraph_function embedding.injection born,
    pushedBirthGraph_oldMeet completion.algebra.union.meet geometry.meet embedding.toMeetEmbeddingCode born oldMeet⟩

theorem externalSeedBirth_entry
    (born : ZFSet.IsFunc (completion.algebra.union.fields 0) times birth)
    {x y t : ZFSet.{u}} (copied : ZFSet.pair x y ∈ completion.externalIdentityCopyGraph P0 r0 μ0 A0) :
    ZFSet.pair y t ∈ old ↔ ZFSet.pair x t ∈ birth :=
  pushedHeightGraph_entry
    (data.externalIdentityCopy_ideal group oldAction pairing unions powers separation infinite hG).injection born copied

end PartitionPilot.Forcing.GroundExternalGeometryInputs

end



namespace PartitionPilot.Forcing.GroundExternalGeometryInputs
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 oldTimes oldBirth : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
variable (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
local notation "P" => completion.externalSeedCarrier P0 r0 μ0 A0
local notation "B" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "old" => completion.externalSeedBirth P0 r0 μ0 A0 oldTimes oldBirth
include data group oldAction pairing unions powers separation collection infinite hG hP0

theorem exists_externalBirths_of_seed (hOldTimes : oldTimes ∈ M.sets)
    (ordinal : ordinalSetProperty oldTimes) (hOldBirth : oldBirth ∈ M.sets)
    (born : ZFSet.IsFunc (completion.algebra.union.fields 0) oldTimes oldBirth)
    (oldMeet : OldMeetCode (completion.algebra.union.fields 1) (completion.algebra.union.fields 2) oldBirth) :
    Nonempty (GroundExternalBirthData M initial I Sources Reps G m one T τ
      P0 r0 μ0 A0 oldTimes oldBirth completion) := by
  obtain ⟨stamps, hStamps, limit, hLimit, _, stampCode⟩ :=
    M.exists_groundCompressionStamps pairing unions separation collection infinite hOldTimes ordinal
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  have seed := data.externalSeedBirth_spec group oldAction pairing unions powers separation infinite hG hP0
    hOldTimes hOldBirth born oldMeet
  have levels := data.externalOwnerLevels_ground_function group oldAction pairing unions powers separation infinite hG hP0
  have hP := data.externalSeedCarrier_ground group oldAction pairing unions powers separation infinite hG hP0
  have subset : P ⊆ B := fun _ hx => ((mem_relationImage _ _ _ _).1 hx).1
  have times : oldTimes ⊆ limit := fun _ ht => stampCode.union.subset 0 (compressionStamp_old_mem (Or.inl ht) 0)
  have oldBefore : ∀ x a n t, ZFSet.pair x a ∈ old → ZFSet.pair (natSetCode n) t ∈ stamps → a ∈ t := by
    intro x a n t entry stamp
    rw [(stampCode.entries n t).1 stamp]
    exact compressionStamp_old_mem (Or.inl (ZFSet.pair_mem_prod.1 (seed.2.1.1 entry)).2) n
  refine ⟨{
    stamps := stamps
    limit := limit
    stamps_ground := hStamps
    limit_ground := hLimit
    times := stampCode
    seed_function := seed.2.1
    birth_ground := M.ownerBirthGraph_mem pairing unions powers separation hP geometry.carrier_ground hLimit
      seed.1 levels.1 hStamps (M.omega_mem separation infinite)
    function := ownerBirthGraph_function seed.2.1 subset times levels.2 stampCode.function
    old_meet := ?_
    preserves_seed := ?_ }⟩
  · apply ownerBirthGraph_oldMeet geometry.meet seed.2.1 subset times levels.2 stampCode.ownerStampCode seed.2.2
    · intro x hx y hy lower
      exact data.externalSeedCarrier_lower group oldAction pairing unions powers separation infinite hG hx hy lower
    · exact oldBefore
    · intro x _ y _ n k first second lower
      exact data.externalOwnerLevels_monotone group oldAction pairing unions powers separation infinite hG hP0 lower first second
  · intro x y t copied
    have embedding := data.externalIdentityCopy_ideal group oldAction pairing unions powers separation infinite hG
    have bounds := ZFSet.pair_mem_prod.1 (embedding.injection.function.1 copied)
    have hy : y ∈ P := (mem_relationImage _ _ _ _).2 ⟨bounds.2, x, bounds.1, copied⟩
    exact (ownerBirthGraph_old_iff hy).trans
      (data.externalSeedBirth_entry group oldAction pairing unions powers separation infinite hG born copied)

theorem exists_externalBirths {base originalBirth : ZFSet.{u}}
    (births : GroundCompressionBirthData M initial I Sources Reps G m one T
      completion.algebra.union base originalBirth) :
    Nonempty (GroundExternalBirthData M initial I Sources Reps G m one T τ
      P0 r0 μ0 A0 births.limit births.birth completion) :=
  data.exists_externalBirths_of_seed group oldAction pairing unions powers separation collection infinite hG hP0
    births.limit_ground births.times.ordinal births.birth_ground births.function births.old_meet

end PartitionPilot.Forcing.GroundExternalGeometryInputs



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundBoundedExternalBirths
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

open SetFormula
universe u
namespace GroundExternalHeightData
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ P0 r0 μ0 A0 C D rD lo hi seed : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (heights : GroundExternalHeightData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 C D rD lo hi seed completion)

theorem attained_columns_below : ∀ a ∈ heightColumns (completion.externalPointCarrier P0 r0 μ0 A0) C D heights.height,
    a ∈ heights.columns.cap := by
  intro a ha
  obtain ⟨_, value, member, projection⟩ := (mem_relationImage _ _ _ _).1 ha
  obtain ⟨b, _, q, _, equal⟩ := (mem_productFirst C D _).1 projection
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
  obtain ⟨_, x, _, entry⟩ := (mem_relationImage _ _ _ _).1 member
  exact heights.below_cap x a q entry

end GroundExternalHeightData

namespace GroundExternalHeightData
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ P0 r0 μ0 A0 C D rD lo hi seed : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (heights : GroundExternalHeightData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 C D rD lo hi seed completion)

theorem boundedData
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (geometry : GroundExternalGeometryData M initial I Sources Reps G m one T τ P0 r0 μ0 A0 completion)
    (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hlo : lo ∈ D) :
    GroundBoundedExternalHeightData M initial I Sources Reps G m one T τ P0 r0 μ0 A0 C D rD lo hi seed completion heights := by
  have hCap := M.transitive hC heights.columns.code.cap_mem
  have hLo := M.transitive hD hlo
  have capPoint := M.orderedPair_mem pairing hCap hLo
  have range : relationImage (completion.externalBoundedCarrier P0 r0 μ0 A0) (ZFSet.prod C D) heights.boundedHeight =
      insert (ZFSet.pair heights.columns.cap lo)
        (relationImage (completion.externalPointCarrier P0 r0 μ0 A0) (ZFSet.prod C D) heights.height) :=
    fixedTopHeightGraph_range heights.code.function heights.columns.code.cap_mem hlo
  refine ⟨M.fixedTopHeightGraph_mem pairing unions geometry.carrier_ground heights.height_ground hCap hLo,
    fixedTopHeightGraph_strict heights.code geometry.meet.order heights.columns.code.cap_mem hlo heights.attained_columns_below,
    fun _ hx _ => fixedTopHeightGraph_old_iff hx,
    fun _ => fixedTopHeightGraph_top_iff heights.code.function,
    range, ?_, ?_, ?_, ?_⟩
  · rw [range]
    exact M.insert_mem pairing unions capPoint heights.range_ground
  · rw [range]
    exact M.groundEmbeddable_insert pairing unions powers separation infinite heights.range_ground capPoint heights.range_countable
  · intro x y z copied
    have raw := copied
    dsimp only [GroundCompressionCompletion.externalIdentityCopyGraph,
      GroundCompressionCompletion.externalCopyGraph, flatCopyEmbeddingGraph] at raw
    have hy : y ∈ completion.externalPointCarrier P0 r0 μ0 A0 :=
      (ZFSet.pair_mem_prod.1 (ZFSet.mem_sep.1 raw).1).2
    exact (fixedTopHeightGraph_old_iff hy).trans (heights.preserves_seed x y z copied)
  · intro x y entry
    exact fixedTopHeightGraph_bound heights.code.function heights.columns.code.cap_mem hlo heights.attained_columns_below entry

end GroundExternalHeightData

namespace GroundExternalBirthData
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ P0 r0 μ0 A0 oldTimes oldBirth : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 oldTimes oldBirth completion)

theorem boundedData
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (geometry : GroundExternalGeometryData M initial I Sources Reps G m one T τ P0 r0 μ0 A0 completion) :
    GroundBoundedExternalBirthData M initial I Sources Reps G m one T τ
      P0 r0 μ0 A0 oldTimes oldBirth completion births := by
  have earlier : ∀ x t, ZFSet.pair x t ∈ births.birth → t ∈ births.limit :=
    fun _ _ entry => (ZFSet.pair_mem_prod.1 (births.function.1 entry)).2
  have retarget := isFunc_retarget_of_entries (C := insert births.limit births.limit) births.function
    (fun x t entry => ZFSet.mem_insert_iff.2 (Or.inr (earlier x t entry)))
  have single := M.fixedTopBirth_singleton_small pairing geometry.carrier_ground
  refine ⟨M.insert_mem pairing unions births.limit_ground births.limit_ground,
    M.fixedTopBirth_mem pairing unions geometry.carrier_ground births.birth_ground births.limit_ground,
    fixedTopBirth_function retarget (ZFSet.mem_insert_iff.2 (Or.inl rfl)),
    fixedTopBirth_oldMeet geometry.meet births.function earlier births.old_meet,
    fun _ hx _ => fixedTopBirth_old_iff hx, fun _ => fixedTopBirth_top_iff births.function,
    fun _ => fixedTopBirth_new_time_iff earlier,
    fun x t entry => (fixedTopBirth_bound earlier x t entry).symm, ?_, single.1, single.2⟩
  intro x y t copied
  have raw := copied
  dsimp only [GroundCompressionCompletion.externalIdentityCopyGraph,
    GroundCompressionCompletion.externalCopyGraph, flatCopyEmbeddingGraph] at raw
  have hy : y ∈ completion.externalPointCarrier P0 r0 μ0 A0 :=
    (ZFSet.pair_mem_prod.1 (ZFSet.mem_sep.1 raw).1).2
  exact (fixedTopBirth_old_iff hy).trans (births.preserves_seed x y t copied)

end GroundExternalBirthData

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundExternalProfilePreservation
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace GroundExternalGeometryInputs
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 Filters : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (origin : GroundCompressionOrigin M initial P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters)
variable (group : GroupCode G m inv one) (action : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets) (hP0 : P0 ∈ M.sets)
variable (initialDomain : initial.D = P0) (initialOrder : initial.rD = r0)
local notation "B" => completion.externalBoundedCarrier P0 r0 μ0 A0
local notation "rB" => completion.externalBoundedOrder P0 r0 μ0 A0
local notation "embedding" => completion.externalOriginalEmbedding P0 r0 μ0 A0
include data origin group action pairing unions powers separation infinite hI hSources hReps hG hT hP0 initialDomain initialOrder

theorem exists_externalOriginal_bottom {b : ZFSet.{u}} (hb : b ∈ P0)
    (least : ∀ x ∈ P0, ZFSet.pair b x ∈ r0) :
    ∃ b' ∈ M.sets, ZFSet.pair b b' ∈ embedding ∧ b' ∈ B ∧
      ∀ y ∈ B, ZFSet.pair b' y ∈ rB := by
  have code := data.externalOriginalEmbedding_code group action pairing unions powers separation infinite hG hP0
  obtain ⟨b', image, _⟩ := code.injection.function.2 b hb
  have bottom := data.externalOriginalEmbedding_bottom origin group action pairing unions powers separation infinite
    hI hSources hReps hG hT hP0 initialDomain initialOrder least image
  have geometry := data.externalBoundedGeometryData group action pairing unions powers separation infinite hG hP0
  exact ⟨b', M.transitive geometry.carrier_ground bottom.1, image, bottom⟩

end GroundExternalGeometryInputs

namespace GroundExternalGeometryInputs
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P r μ A : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P r μ A completion)
variable (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP : P ∈ M.sets)
include data group action pairing unions powers separation infinite hG hP

theorem externalOriginal_image_mem {x y : ZFSet.{u}}
    (entry : ZFSet.pair x y ∈ completion.externalOriginalEmbedding P r μ A) :
    y ∈ completion.externalPointCarrier P r μ A := by
  have copied := ((completion.externalOriginalEmbedding_entry_iff P r μ A x y).1 entry).1
  have geometry := data.externalGeometryData group action pairing unions powers separation infinite hG hP
  exact (ZFSet.pair_mem_prod.1
    ((geometry.copies _ data.group.group_code.identity_mem).injection.function.1 copied)).2

theorem externalOriginal_top_strict {x y : ZFSet.{u}}
    (entry : ZFSet.pair x y ∈ completion.externalOriginalEmbedding P r μ A) :
    ZFSet.pair y (completion.externalPointCarrier P r μ A) ∈ completion.externalBoundedOrder P r μ A ∧
    ZFSet.pair (completion.externalPointCarrier P r μ A) y ∉ completion.externalBoundedOrder P r μ A := by
  have hy := data.externalOriginal_image_mem group action pairing unions powers separation infinite hG hP entry
  have geometry := data.externalBoundedGeometryData group action pairing unions powers separation infinite hG hP
  exact ⟨geometry.greatest y (ZFSet.mem_insert_of_mem _ hy), geometry.strict_top y hy⟩

end GroundExternalGeometryInputs

open SetFormula
universe u

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundInitialExternalHeights
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
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
local notation "C" => M.groundOmegaOne pairing unions powers separation collection infinite
include pairing unions powers separation collection infinite choice

theorem exists_externalColumns {K : ZFSet.{u}} (hK : K ∈ M.sets)
    (subset : K ⊆ C) (small : M.groundEmbeddable K ZFSet.omega) :
    Nonempty (GroundExternalColumnData M C K) := by
  have spec := M.groundOmegaOne_spec pairing unions powers separation collection infinite
  have omega := M.omega_mem separation infinite
  obtain ⟨base, hBase, above⟩ := M.groundOmegaOne_countable_bound
    pairing unions powers separation collection infinite choice hK subset small
  obtain ⟨sequence, hSequence, _, _, _, stamps⟩ := M.exists_groundCompressionStamps
    pairing unions separation collection infinite (M.transitive spec.1 hBase) ((spec.2.2.1 base).1 hBase).2.1
  have valueMember (n : Nat) : compressionStamp base n ∈ C := by
    induction n with
    | zero => exact M.groundOmegaOne_successor pairing unions powers separation collection infinite hBase
    | succ n ih => exact M.groundOmegaOne_successor pairing unions powers separation collection infinite ih
  have function : ZFSet.IsFunc ZFSet.omega C sequence := by
    refine ⟨?_, stamps.function.2⟩
    intro z hz
    obtain ⟨n, hn, a, _, rfl⟩ := ZFSet.mem_prod.1 (stamps.function.1 hz)
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
    exact ZFSet.pair_mem_prod.2 ⟨natSetCode_mem_omega n, (stamps.entries n a).1 hz ▸ valueMember n⟩
  have injection := successorColumnGraph_injection function stamps.entries
  have rangeGround := M.relationImage_mem separation omega spec.1 hSequence
  have inverseGround := M.relationConverse_mem pairing unions powers separation omega spec.1 hSequence
  have rangeSmall : M.groundEmbeddable (relationImage ZFSet.omega C sequence) ZFSet.omega :=
    ⟨relationConverse ZFSet.omega C sequence, inverseGround, injection.converse_image⟩
  obtain ⟨cap, hCap, bounded⟩ := M.groundOmegaOne_countable_bound
    pairing unions powers separation collection infinite choice rangeGround
    (fun _ hz => ((mem_relationImage _ _ _ _).1 hz).1) rangeSmall
  refine ⟨⟨base, sequence, cap, hSequence,
    ⟨function, stamps.entries, hBase, hCap, above, ?_⟩,
    rangeGround, inverseGround, injection.converse_image⟩⟩
  intro n
  exact bounded _ ((mem_relationImage _ _ _ _).2
    ⟨valueMember n, natSetCode n, natSetCode_mem_omega n, (stamps.entries n _).2 rfl⟩)

theorem exists_externalHeightColumns {P D old : ZFSet.{u}}
    (hP : P ∈ M.sets) (hD : D ∈ M.sets) (hOld : old ∈ M.sets)
    (small : M.groundEmbeddable (relationImage P (ZFSet.prod C D) old) ZFSet.omega) :
    Nonempty (GroundExternalColumnData M C (heightColumns P C D old)) := by
  have hC := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
  exact M.exists_externalColumns pairing unions powers separation collection infinite choice
    (M.heightColumns_mem pairing unions powers separation hP hC hD hOld)
    (fun _ hz => ((mem_relationImage _ _ _ _).1 hz).1)
    (M.heightColumns_countable pairing unions powers separation infinite choice hP hC hD hOld small)

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.GroundExternalGeometryInputs
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 C D rD lo hi original : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets)
variable (ordinal : ordinalSetProperty C)
variable (heights : GroundCompressionHeightData M initial I Sources Reps G m one T completion.algebra.union P0 C D rD original)
variable (localHeights : GroundExternalLocalHeightData M initial I Sources Reps G m one T τ P0 r0 μ0 A0 D rD lo hi completion)
local notation "B" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "P" => completion.externalSeedCarrier P0 r0 μ0 A0
variable (columns : GroundExternalColumnData M C
  (heightColumns (completion.externalSeedCarrier P0 r0 μ0 A0) C D
    (completion.externalSeedHeight P0 r0 μ0 A0 C D heights.height)))
include data group oldAction pairing unions powers separation infinite choice hG hP0 hC hD ordinal heights localHeights columns

theorem externalHeightData_of_families (coordinateSmall : M.groundEmbeddable D ZFSet.omega) :
    Nonempty (GroundExternalHeightData M initial I Sources Reps G m one T τ
      P0 r0 μ0 A0 C D rD lo hi heights.height completion) := by
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  have seed := data.externalSeedHeights_spec group oldAction pairing unions powers separation infinite hG hP0 heights hC hD
  have owner := data.externalStarOwner_ground_function group oldAction pairing unions powers separation infinite hG hP0
  have depth := data.externalStarDepth_ground_function group oldAction pairing unions powers separation infinite hG
  have vertices := (data.externalStarCarriers_ground pairing unions powers separation hG).1
  have coordGround := data.externalTileCoordinates_ground group oldAction pairing unions powers separation infinite hG localHeights hP0 hD
  have coordPartial := data.externalTileCoordinates_partial group oldAction pairing unions powers separation infinite hG localHeights hP0
  have coordTotal := data.externalTileCoordinates_owner_total group oldAction pairing unions powers separation infinite hG localHeights
  have coordStrict := data.externalTileCoordinates_raw_strict group oldAction pairing unions powers separation infinite hG localHeights
  have seedCode := seed.2.2.1
  have subset : P ⊆ B := fun _ hx => ((mem_relationImage _ _ _ _).1 hx).1
  have heightGround : localHeights.externalHeightGraph C heights.height columns.sequence ∈ M.sets :=
    M.externalOwnerHeightGraph_mem pairing unions powers separation seed.1 geometry.carrier_ground vertices hC hD
      seed.2.1 owner.1 depth.1 columns.sequence_ground coordGround (M.omega_mem separation infinite)
  have strict : StrictLexHeightCode B C D (completion.externalPointOrder P0 r0 μ0 A0)
      (localHeights.externalHeightGraph C heights.height columns.sequence) rD := by
    apply externalOwnerHeightGraph_strictLex subset seedCode owner.2 depth.2 columns.code coordPartial coordTotal
    · intro x hx fresh y hy
      exact data.externalSeedCarrier_no_new_below group oldAction pairing unions powers separation infinite hG hx fresh hy
    · intro x _ _ y _ _ v w n m first second firstDepth secondDepth lower
      exact (data.externalStarOwner_order group oldAction pairing unions powers separation infinite hG
        lower first second firstDepth secondDepth).1
    · intro x _ _ y _ _ v w n first second firstDepth secondDepth lower
      exact (data.externalStarOwner_order group oldAction pairing unions powers separation infinite hG
        lower first second firstDepth secondDepth).2 rfl
    · exact coordStrict
  have rangeSmall := M.externalOwnerHeightGraph_range_small pairing unions powers separation infinite choice
    seed.1 geometry.carrier_ground hC hD seed.2.1 columns.sequence_ground heightGround seedCode.function
    seed.2.2.2.2 ⟨_, columns.inverse_ground, columns.inverse_code⟩ coordinateSmall
  refine ⟨{
    localHeights := localHeights
    columns := columns
    height_ground := heightGround
    code := strict
    range_ground := rangeSmall.1
    range_countable := rangeSmall.2
    preserves_seed := ?_
    below_cap := ?_ }⟩
  · intro x y z copied
    have embedding := data.externalIdentityCopy_ideal group oldAction pairing unions powers separation infinite hG
    have bounds := ZFSet.pair_mem_prod.1 (embedding.injection.function.1 copied)
    have hy : y ∈ P := (mem_relationImage _ _ _ _).2 ⟨bounds.2, x, bounds.1, copied⟩
    exact (externalOwnerHeightGraph_old hy).trans (pushedHeightGraph_entry embedding.injection heights.code.function copied)
  · intro x a d entry
    rcases (pair_mem_externalOwnerHeightGraph _ _ _ _ _ _ _ _ _ _ _ _).1 entry with retained | fresh
    · have below := columns.code.old_below (mem_heightColumns_of_entry seedCode.function retained) 0
      exact ordinal.2 columns.cap columns.code.cap_mem (compressionStamp columns.base 0)
        (columns.code.cap_bound 0) a below
    · obtain ⟨_, _, _, _, n, hn, a', _, d', _, equal, _, _, column, _⟩ := fresh
      obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
      obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
      exact (columns.code.entries n a).1 column ▸ columns.code.cap_bound n

end PartitionPilot.Forcing.GroundExternalGeometryInputs

namespace PartitionPilot.Forcing.GroundExternalGeometryInputs
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 D rD lo hi original c : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
variable (heights : GroundCompressionHeightData M initial I Sources Reps G m one T
  completion.algebra.union P0 (M.groundOmegaOne pairing unions powers separation collection infinite) D rD original)
variable (target : DenseOrderCode D rD) (injection : InjectionCode D ZFSet.omega c)
variable (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) (hc : c ∈ M.sets)
variable (hlo : lo ∈ D) (hhi : hi ∈ D) (gap : ZFSet.pair lo hi ∈ rD)
include data group oldAction pairing unions powers separation collection infinite choice hG hP0
  heights target injection hD hrD hc hlo hhi gap

theorem exists_externalHeight :
    Nonempty (GroundExternalHeightData M initial I Sources Reps G m one T τ P0 r0 μ0 A0
      (M.groundOmegaOne pairing unions powers separation collection infinite) D rD lo hi
      heights.height completion) := by
  have omegaOne := M.groundOmegaOne_spec pairing unions powers separation collection infinite
  obtain ⟨localHeights⟩ := data.exists_localHeightFamily group oldAction pairing unions powers
    separation collection infinite hG hP0 heights omegaOne.2.1 target.toStrictLinearOrderCode
    omegaOne.1 hD hrD target injection hD hrD hc hlo hhi gap choice
  have seed := data.externalSeedHeights_spec group oldAction pairing unions powers separation infinite
    hG hP0 heights omegaOne.1 hD
  obtain ⟨columns⟩ := M.exists_externalHeightColumns pairing unions powers separation collection infinite
    choice seed.1 hD seed.2.1 seed.2.2.2.2
  exact data.externalHeightData_of_families group oldAction pairing unions powers separation infinite
    choice hG hP0 omegaOne.1 hD omegaOne.2.1 heights localHeights columns ⟨c, hc, injection⟩

end PartitionPilot.Forcing.GroundExternalGeometryInputs

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
local notation "C" => M.groundOmegaOne pairing unions powers separation collection infinite

include choice in
theorem exists_groundInitialExternalHeights
    {P G r μ A Labels m inv one τ D rD c original base old T0 : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (hm : m ∈ M.sets) (hInv : inv ∈ M.sets)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) (hτ : τ ∈ P)
    (top : ∀ x ∈ P, ZFSet.pair x τ ∈ r)
    (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (hc : c ∈ M.sets) (hOriginal : original ∈ M.sets)
    (originalCode : StrictLexHeightCode P C D r original rD)
    (target : DenseOrderCode D rD)
    (above : ∀ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD)
    (coordinateInjection : InjectionCode D ZFSet.omega c)
    (originalSmall : M.groundEmbeddable (relationImage P (ZFSet.prod C D) original) ZFSet.omega)
    (hBase : base ∈ M.sets) (prior : GroundChronologicalHistory M T0 C D rD)
    (ordinal : ordinalSetProperty T0) (baseMember : base ∈ T0)
    (priorSpace : prior.space base = P) (priorOrder : prior.order base = r)
    (priorMeet : prior.meetGraph base = μ) (priorBirth : prior.birth base = old)
    (priorHeight : prior.height base = original) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let Sources := literalTaskSourceGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let Filters := literalTaskFilterGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let Targets := literalTaskTargetGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let Separators := literalTaskSeparatorGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let T := M.groundTaskTransport P G r μ A Labels
    I ∈ M.sets ∧ Sources ∈ M.sets ∧ Filters ∈ M.sets ∧ T ∈ M.sets ∧
      ∃ Reps ∈ M.sets,
        ∃ _origin : GroundCompressionOrigin M (M.initialCompressionData P G r μ A Labels)
          P r μ A τ I Sources Reps G m inv one T Filters,
        ∃ compression : GroundChronologicalCompression M (M.initialCompressionData P G r μ A Labels)
          I Sources Reps G m one T τ P C D rD original Targets Separators Filters base old T0 prior,
          GroundExternalGeometryInputs M (M.initialCompressionData P G r μ A Labels)
            I Sources Reps G m inv one T τ P r μ A compression.born.profiled.heighted.completion ∧
          GroundExternalGeometryData M (M.initialCompressionData P G r μ A Labels)
            I Sources Reps G m one T τ P r μ A compression.born.profiled.heighted.completion ∧
          GroundExternalBoundedGeometryData M (M.initialCompressionData P G r μ A Labels)
            I Sources Reps G m one T τ P r μ A compression.born.profiled.heighted.completion ∧
          ∃ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD ∧
            ∃ heights : GroundExternalHeightData M (M.initialCompressionData P G r μ A Labels)
              I Sources Reps G m one T τ P r μ A C D rD lo hi
              compression.born.profiled.heighted.heights.height compression.born.profiled.heighted.completion,
              GroundBoundedExternalHeightData M (M.initialCompressionData P G r μ A Labels)
                I Sources Reps G m one T τ P r μ A C D rD lo hi
                compression.born.profiled.heighted.heights.height compression.born.profiled.heighted.completion heights := by
  have omegaOne := M.groundOmegaOne_spec pairing unions powers separation collection infinite
  obtain ⟨z, originalEntry, _⟩ := originalCode.function.2 τ hτ
  have hz := (ZFSet.pair_mem_prod.1 (originalCode.function.1 originalEntry)).2
  obtain ⟨a, _, lo, hlo, rfl⟩ := ZFSet.mem_prod.1 hz
  obtain ⟨hi, hhi, gap⟩ := above lo hlo
  dsimp only
  obtain ⟨hI, hSources, hFilters, hT, Reps, hReps, origin, compression, data, geometry, bounded⟩ :=
    M.exists_groundInitialExternalBoundedGeometry pairing unions powers separation collection infinite choice
      hP hG hr hμ hA hLabels hm hInv group action meet hτ top omegaOne.1 hD hrD hc hOriginal
      originalCode omegaOne.2.1 target above coordinateInjection originalSmall hBase prior ordinal baseMember
      priorSpace priorOrder priorMeet priorBirth priorHeight
  obtain ⟨heights⟩ := data.exists_externalHeight group action pairing unions powers separation collection infinite choice
    hG hP compression.born.profiled.heighted.heights target coordinateInjection hD hrD hc hlo hhi gap
  exact ⟨hI, hSources, hFilters, hT, Reps, hReps, origin, compression, data, geometry, bounded,
    lo, hlo, hi, hhi, gap, heights,
    heights.boundedData pairing unions powers separation infinite geometry omegaOne.1 hD hlo⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundInitialExternalBirths
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

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
local notation "C" => M.groundOmegaOne pairing unions powers separation collection infinite

include choice in
theorem exists_groundInitialExternalBirths
    {P G r μ A Labels m inv one τ D rD c original base old T0 : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (hm : m ∈ M.sets) (hInv : inv ∈ M.sets)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) (hτ : τ ∈ P)
    (top : ∀ x ∈ P, ZFSet.pair x τ ∈ r)
    (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (hc : c ∈ M.sets) (hOriginal : original ∈ M.sets)
    (originalCode : StrictLexHeightCode P C D r original rD)
    (target : DenseOrderCode D rD)
    (above : ∀ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD)
    (coordinateInjection : InjectionCode D ZFSet.omega c)
    (originalSmall : M.groundEmbeddable (relationImage P (ZFSet.prod C D) original) ZFSet.omega)
    (hBase : base ∈ M.sets) (prior : GroundChronologicalHistory M T0 C D rD)
    (ordinal : ordinalSetProperty T0) (baseMember : base ∈ T0)
    (priorSpace : prior.space base = P) (priorOrder : prior.order base = r)
    (priorMeet : prior.meetGraph base = μ) (priorBirth : prior.birth base = old)
    (priorHeight : prior.height base = original) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let Sources := literalTaskSourceGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let Filters := literalTaskFilterGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let Targets := literalTaskTargetGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let Separators := literalTaskSeparatorGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let T := M.groundTaskTransport P G r μ A Labels
    I ∈ M.sets ∧ Sources ∈ M.sets ∧ Filters ∈ M.sets ∧ T ∈ M.sets ∧
      ∃ Reps ∈ M.sets,
        ∃ _origin : GroundCompressionOrigin M (M.initialCompressionData P G r μ A Labels)
          P r μ A τ I Sources Reps G m inv one T Filters,
        ∃ compression : GroundChronologicalCompression M (M.initialCompressionData P G r μ A Labels)
          I Sources Reps G m one T τ P C D rD original Targets Separators Filters base old T0 prior,
          GroundExternalGeometryInputs M (M.initialCompressionData P G r μ A Labels)
            I Sources Reps G m inv one T τ P r μ A compression.born.profiled.heighted.completion ∧
          GroundExternalGeometryData M (M.initialCompressionData P G r μ A Labels)
            I Sources Reps G m one T τ P r μ A compression.born.profiled.heighted.completion ∧
          GroundExternalBoundedGeometryData M (M.initialCompressionData P G r μ A Labels)
            I Sources Reps G m one T τ P r μ A compression.born.profiled.heighted.completion ∧
          ∃ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD ∧
            ∃ heights : GroundExternalHeightData M (M.initialCompressionData P G r μ A Labels)
              I Sources Reps G m one T τ P r μ A C D rD lo hi
              compression.born.profiled.heighted.heights.height compression.born.profiled.heighted.completion,
              GroundBoundedExternalHeightData M (M.initialCompressionData P G r μ A Labels)
                I Sources Reps G m one T τ P r μ A C D rD lo hi
                compression.born.profiled.heighted.heights.height compression.born.profiled.heighted.completion heights ∧
              ∃ births : GroundExternalBirthData M (M.initialCompressionData P G r μ A Labels)
                I Sources Reps G m one T τ P r μ A compression.born.births.limit compression.born.births.birth
                compression.born.profiled.heighted.completion,
                GroundBoundedExternalBirthData M (M.initialCompressionData P G r μ A Labels)
                  I Sources Reps G m one T τ P r μ A compression.born.births.limit compression.born.births.birth
                  compression.born.profiled.heighted.completion births := by
  dsimp only
  obtain ⟨hI, hSources, hFilters, hT, Reps, hReps, origin, compression, data, geometry,
      boundedGeometry, lo, hlo, hi, hhi, gap, heights, boundedHeights⟩ :=
    M.exists_groundInitialExternalHeights pairing unions powers separation collection infinite choice
      hP hG hr hμ hA hLabels hm hInv group action meet hτ top hD hrD hc hOriginal
      originalCode target above coordinateInjection originalSmall hBase prior ordinal baseMember
      priorSpace priorOrder priorMeet priorBirth priorHeight
  obtain ⟨births⟩ := data.exists_externalBirths group action pairing unions powers separation collection infinite
    hG hP compression.born.births
  exact ⟨hI, hSources, hFilters, hT, Reps, hReps, origin, compression, data, geometry,
    boundedGeometry, lo, hlo, hi, hhi, gap, heights, boundedHeights, births,
    births.boundedData pairing unions geometry⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundInitialExternalChronology
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

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
local notation "C" => M.groundOmegaOne pairing unions powers separation collection infinite

include choice in
theorem exists_groundInitialExternalChronology
    {P G r μ A Labels m inv one τ D rD c original base old T0 : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (hm : m ∈ M.sets) (hInv : inv ∈ M.sets)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) (hτ : τ ∈ P)
    (top : ∀ x ∈ P, ZFSet.pair x τ ∈ r)
    (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (hc : c ∈ M.sets) (hOriginal : original ∈ M.sets)
    (originalCode : StrictLexHeightCode P C D r original rD)
    (target : DenseOrderCode D rD)
    (above : ∀ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD)
    (coordinateInjection : InjectionCode D ZFSet.omega c)
    (originalSmall : M.groundEmbeddable (relationImage P (ZFSet.prod C D) original) ZFSet.omega)
    (hBase : base ∈ M.sets) (prior : GroundChronologicalHistory M T0 C D rD)
    (ordinal : ordinalSetProperty T0) (baseMember : base ∈ T0)
    (priorSpace : prior.space base = P) (priorOrder : prior.order base = r)
    (priorMeet : prior.meetGraph base = μ) (priorBirth : prior.birth base = old)
    (priorHeight : prior.height base = original) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let Sources := literalTaskSourceGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let Filters := literalTaskFilterGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let Targets := literalTaskTargetGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let Separators := literalTaskSeparatorGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let T := M.groundTaskTransport P G r μ A Labels
    I ∈ M.sets ∧ Sources ∈ M.sets ∧ Filters ∈ M.sets ∧ T ∈ M.sets ∧
      ∃ Reps ∈ M.sets,
        ∃ _origin : GroundCompressionOrigin M (M.initialCompressionData P G r μ A Labels)
          P r μ A τ I Sources Reps G m inv one T Filters,
        ∃ compression : GroundChronologicalCompression M (M.initialCompressionData P G r μ A Labels)
          I Sources Reps G m one T τ P C D rD original Targets Separators Filters base old T0 prior,
          GroundExternalGeometryInputs M (M.initialCompressionData P G r μ A Labels)
            I Sources Reps G m inv one T τ P r μ A compression.born.profiled.heighted.completion ∧
          GroundExternalGeometryData M (M.initialCompressionData P G r μ A Labels)
            I Sources Reps G m one T τ P r μ A compression.born.profiled.heighted.completion ∧
          GroundExternalBoundedGeometryData M (M.initialCompressionData P G r μ A Labels)
            I Sources Reps G m one T τ P r μ A compression.born.profiled.heighted.completion ∧
          ∃ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD ∧
            ∃ heights : GroundExternalHeightData M (M.initialCompressionData P G r μ A Labels)
              I Sources Reps G m one T τ P r μ A C D rD lo hi
              compression.born.profiled.heighted.heights.height compression.born.profiled.heighted.completion,
              GroundBoundedExternalHeightData M (M.initialCompressionData P G r μ A Labels)
                I Sources Reps G m one T τ P r μ A C D rD lo hi
                compression.born.profiled.heighted.heights.height compression.born.profiled.heighted.completion heights ∧
              ∃ births : GroundExternalBirthData M (M.initialCompressionData P G r μ A Labels)
                I Sources Reps G m one T τ P r μ A compression.born.births.limit compression.born.births.birth
                compression.born.profiled.heighted.completion,
                GroundBoundedExternalBirthData M (M.initialCompressionData P G r μ A Labels)
                  I Sources Reps G m one T τ P r μ A compression.born.births.limit compression.born.births.birth
                  compression.born.profiled.heighted.completion births ∧
                Nonempty (GroundChronologicalExternal M (M.initialCompressionData P G r μ A Labels)
                  I Sources Reps G m inv one T τ P r μ A compression.born.births.limit compression.born.births.birth
                  C D rD lo hi compression.born.profiled.heighted.heights.height
                  (insert compression.born.births.limit compression.born.births.limit)
                  compression.born.profiled.heighted.completion births heights compression.history) := by
  dsimp only
  obtain ⟨hI, hSources, hFilters, hT, Reps, hReps, origin, compression, data, geometry,
      boundedGeometry, lo, hlo, hi, hhi, gap, heights, boundedHeights, births, boundedBirths⟩ :=
    M.exists_groundInitialExternalBirths pairing unions powers separation collection infinite choice
      hP hG hr hμ hA hLabels hm hInv group action meet hτ top hD hrD hc hOriginal
      originalCode target above coordinateInjection originalSmall hBase prior ordinal baseMember
      priorSpace priorOrder priorMeet priorBirth priorHeight
  let chronological := births.chronologicalData heights compression.history data group action
    pairing unions powers separation infinite hG hP
    (ordinalSetProperty_succ compression.born.births.times.ordinal)
    (ZFSet.mem_insert_iff.2 (Or.inl rfl))
    compression.limit_values.1 compression.limit_values.2.1 compression.limit_values.2.2.1
    compression.limit_values.2.2.2.1 compression.born.births.function boundedHeights
  exact ⟨hI, hSources, hFilters, hT, Reps, hReps, origin, compression, data, geometry,
    boundedGeometry, lo, hlo, hi, hhi, gap, heights, boundedHeights, births, boundedBirths,
    ⟨chronological⟩⟩

end PartitionPilot.Forcing.TransitiveGround

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

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)

include choice in
theorem exists_groundInitialMainSuccessor_oai {D rD Labels c : ZFSet.{u}}
    (source : GroundChronologicalMainStage M
      (M.groundOmegaOne pairing unions powers separation collection infinite) D rD)
    (hLabels : Labels ∈ M.sets) (hc : c ∈ M.sets)
    (dense : DenseOrderCode D rD)
    (above : ∀ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD)
    (coordinateInjection : InjectionCode D ZFSet.omega c) :
    Nonempty (GroundInitialMainSuccessorData M
      (M.groundOmegaOne pairing unions powers separation collection infinite) D rD source Labels) := by
  obtain ⟨hI, hSources, hFilters, hT, Reps, hReps, origin, compression, _data, geometry,
      boundedGeometry, lo, hlo, hi, hhi, gap, heights, boundedHeights, births, boundedBirths,
      ⟨external⟩⟩ :=
    M.exists_groundInitialExternalChronology pairing unions powers separation collection infinite choice
      source.stage.carrier_ground source.stage.actors_ground source.stage.order_ground source.stage.meet_ground
      source.stage.action_ground hLabels source.stage.multiplication_ground source.stage.inverse_ground
      source.stage.group_code source.stage.action_code source.stage.meet source.stage.top_mem source.stage.greatest
      source.stage.coordinates_ground source.stage.coordinate_order_ground hc source.stage.height_ground
      source.stage.height_code dense above coordinateInjection source.stage.height_range_countable
      source.cutoff_ground source.history (ordinalSetProperty_succ source.cutoff_ordinal)
      (ZFSet.mem_insert _ _) source.carrier_eq source.order_eq source.meet_eq rfl source.height_eq
  obtain ⟨b', hb', image, _bottom⟩ :=
    external.inputs.exists_externalOriginal_bottom origin source.stage.group_code source.stage.action_code
      pairing unions powers separation infinite hI hSources hReps source.stage.actors_ground hT
      source.stage.carrier_ground rfl rfl source.stage.bottom_mem source.stage.least
  let target := external.toMainStage origin source.stage.group_code source.stage.action_code
    pairing unions powers separation infinite hI hSources hReps source.stage.actors_ground hT
    source.stage.carrier_ground rfl rfl boundedHeights source.stage.columns_ground
    source.stage.coordinates_ground source.stage.coordinate_order_ground source.stage.least image
  let transition := source.externalTransition compression external origin pairing unions powers separation infinite
    hI hSources hReps hT rfl rfl boundedHeights boundedBirths image
  refine ⟨{
    indices_ground := hI
    sources_ground := hSources
    filters_ground := hFilters
    task_action_ground := hT
    Reps := Reps
    representatives_ground := hReps
    origin := origin
    compression := compression
    geometry := geometry
    boundedGeometry := boundedGeometry
    lo := lo
    hi := hi
    lo_mem := hlo
    hi_mem := hhi
    interval := gap
    heights := heights
    boundedHeights := boundedHeights
    births := births
    boundedBirths := boundedBirths
    external := external
    bottomImage := b'
    bottom_ground := hb'
    bottom_entry := image
    target := target
    transition := transition
    cutoff_strict := source.external_cutoff_strict compression
    target_cutoff := rfl
    target_history := HEq.rfl
    target_fields := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    target_birth := external.toMainStage_birth origin source.stage.group_code source.stage.action_code
      pairing unions powers separation infinite hI hSources hReps source.stage.actors_ground hT
      source.stage.carrier_ground rfl rfl boundedHeights source.stage.columns_ground
      source.stage.coordinates_ground source.stage.coordinate_order_ground source.stage.least image
    point_graph := rfl
    actor_graph := rfl
    strict_new_top := ?_ }⟩
  intro x y entry
  exact external.inputs.externalOriginal_top_strict source.stage.group_code source.stage.action_code
    pairing unions powers separation infinite source.stage.actors_ground source.stage.carrier_ground entry

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

theorem solution.{u} : type_of% @OAI.PartitionPilot.Forcing.TransitiveGround.exists_groundInitialMainSuccessor_oai.{u} := @OAI.PartitionPilot.Forcing.TransitiveGround.exists_groundInitialMainSuccessor_oai.{u}
