-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralSuccessor_insert_visibleLift
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:35:20.377134+00:00
-- url     : https://prove2.me/submissions/9c847c8c-4284-40b6-83ec-2e0529833803

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GenericPartialFunctions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing



section

universe u
variable {P : Type u} [Preorder P]

theorem exists_filter_meeting_sequence (p : P) (D : Nat → Set P)
    (dense : ∀ n, Dense (D n)) :
    ∃ H : ConditionFilter P, H.mem p ∧ ∀ n, H.Meets (D n) := by
  classical
  let next (n : Nat) (q : P) : P := Classical.choose (dense n q)
  have next_le (n : Nat) (q : P) : next n q ≤ q := (Classical.choose_spec (dense n q)).1
  have next_mem (n : Nat) (q : P) : next n q ∈ D n := (Classical.choose_spec (dense n q)).2
  let chain : Nat → P := Nat.rec p next
  have step (n : Nat) : chain (n + 1) ≤ chain n := next_le n (chain n)
  have down : Antitone chain := antitone_nat_of_succ_le step
  let H : ConditionFilter P := {
    mem := fun q => ∃ n, chain n ≤ q
    nonempty := ⟨p, 0, le_rfl⟩
    upward := by
      rintro q r ⟨n, nq⟩ qr
      exact ⟨n, nq.trans qr⟩
    directed := by
      rintro q r ⟨n, nq⟩ ⟨m, mr⟩
      exact ⟨chain (max n m), ⟨max n m, le_rfl⟩,
        (down (le_max_left n m)).trans nq, (down (le_max_right n m)).trans mr⟩ }
  exact ⟨H, ⟨0, le_rfl⟩, fun n => ⟨chain (n + 1), ⟨n + 1, le_rfl⟩, next_mem n (chain n)⟩⟩

theorem exists_generic_for_countable_family (p : P) (family : Set (Set P))
    (small : family.Countable) :
    ∃ H : ConditionFilter P, H.mem p ∧ H.GenericFor family := by
  classical
  let listed := Set.enumerateCountable small (Set.univ : Set P)
  let D (n : Nat) : Set P := if Dense (listed n) then listed n else Set.univ
  have dense (n : Nat) : Dense (D n) := by
    dsimp [D]
    split_ifs with h
    · exact h
    · exact fun q => ⟨q, le_rfl, Set.mem_univ q⟩
  obtain ⟨H, hp, meets⟩ := exists_filter_meeting_sequence p D dense
  refine ⟨H, hp, ?_⟩
  intro E hE hDense
  obtain ⟨n, hn⟩ := Set.subset_range_enumerate small (Set.univ : Set P) hE
  have eq : D n = E := by
    dsimp [D, listed]
    simp only [hn, ite_eq_left hDense]
  exact eq ▸ meets n






end



end PartitionPilot.Forcing

end OAI
end

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_CountableCoding
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps

universe u

theorem natPair_upper (a b : Nat) : natPair a b < (a + b + 1) * (a + b + 1) := by
  unfold natPair
  rw [Nat.succ_mul_succ]
  omega

theorem natPair_sum_lt {a b c d : Nat} (less : a + b < c + d) : natPair a b < natPair c d := by
  have step : a + b + 1 ≤ c + d := by omega
  have sq := Nat.mul_le_mul step step
  have bound := natPair_upper a b
  unfold natPair at *
  omega

theorem natPair_injective {a b c d : Nat} (eq : natPair a b = natPair c d) : a = c ∧ b = d := by
  have sums : a + b = c + d := by
    have h₁ : ¬ a + b < c + d := fun h => Nat.ne_of_lt (natPair_sum_lt h) eq
    have h₂ : ¬ c + d < a + b := fun h => Nat.ne_of_lt (natPair_sum_lt h) eq.symm
    omega
  unfold natPair at eq
  rw [sums] at eq
  omega

end PartitionPilot.Compression.RecursiveMaps

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_CountableSetFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing



namespace SetFormula

open Compression.RecursiveMaps

theorem natCode_injective {n : Nat} : Function.Injective (@natCode n) := by
  intro φ
  induction φ with
  | equal i j =>
    intro ψ eq
    cases ψ <;> simp only [natCode] at eq
    · have parts := natPair_injective (natPair_injective eq).2
      exact congrArg₂ SetFormula.equal (Fin.ext parts.1) (Fin.ext parts.2)
    all_goals have bad := (natPair_injective eq).1; omega
  | mem i j =>
    intro ψ eq
    cases ψ <;> simp only [natCode] at eq
    · have bad := (natPair_injective eq).1; omega
    · have parts := natPair_injective (natPair_injective eq).2
      exact congrArg₂ SetFormula.mem (Fin.ext parts.1) (Fin.ext parts.2)
    all_goals have bad := (natPair_injective eq).1; omega
  | neg φ ih =>
    intro ψ eq
    cases ψ <;> simp only [natCode] at eq
    · have bad := (natPair_injective eq).1; omega
    · have bad := (natPair_injective eq).1; omega
    · exact congrArg SetFormula.neg (ih (natPair_injective eq).2)
    all_goals have bad := (natPair_injective eq).1; omega
  | conj φ χ ihφ ihχ =>
    intro ψ eq
    cases ψ <;> simp only [natCode] at eq
    · have bad := (natPair_injective eq).1; omega
    · have bad := (natPair_injective eq).1; omega
    · have bad := (natPair_injective eq).1; omega
    · have parts := natPair_injective (natPair_injective eq).2
      exact congrArg₂ SetFormula.conj (ihφ parts.1) (ihχ parts.2)
    · have bad := (natPair_injective eq).1; omega
  | all φ ih =>
    intro ψ eq
    cases ψ <;> simp only [natCode] at eq
    · have bad := (natPair_injective eq).1; omega
    · have bad := (natPair_injective eq).1; omega
    · have bad := (natPair_injective eq).1; omega
    · have bad := (natPair_injective eq).1; omega
    · exact congrArg SetFormula.all (ih (natPair_injective eq).2)

instance countable (n : Nat) : Countable (SetFormula n) := natCode_injective.countable

end SetFormula

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_CountableFormulaFamilies
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall _root_.OAI.PartitionPilot.Forcing.Name.boundedNames_small _root_.OAI.PartitionPilot.Forcing.Name.unionIndices_small _root_.OAI.PartitionPilot.Forcing.PosetAction.mixIndices_small
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.Name

open SetRealization
universe u
variable {P : Type u} [Preorder P] [Countable P] {s : Presentation P}

theorem atomicFamily_countable (D : NameDomain s) (small : D.names.Countable) :
    (atomicFamily D).Countable := by
  let : Countable D.names := small
  let memSet (z : P × D.names × D.names) := Localized z.1 (MemWitness z.2.1.val z.2.2.val)
  let eqSet (z : D.names × D.names) := EqDecisionWitness z.1.val z.2.val
  apply ((Set.countable_range memSet).union (Set.countable_range eqSet)).mono
  intro E hE
  rcases hE with ⟨p, σ, τ, hσ, hτ, rfl⟩ | ⟨σ, τ, hσ, hτ, rfl⟩
  · exact Or.inl ⟨(p, ⟨σ, hσ⟩, ⟨τ, hτ⟩), rfl⟩
  · exact Or.inr ⟨(⟨σ, hσ⟩, ⟨τ, hτ⟩), rfl⟩

end PartitionPilot.Forcing.Name

namespace PartitionPilot.Forcing.SetFormula

open SetRealization
universe u
variable {P : Type u} [Preorder P] [Countable P] {s : Presentation P}

theorem formulaFamily_countable (D : Name.NameDomain s) (small : D.names.Countable) :
    (formulaFamily D).Countable := by
  let : Countable D.names := small
  let decisions (z : Σ n, SetFormula n × Assignment D n) := DecisionWitness D z.2.1 z.2.2
  let universals (z : Σ n, SetFormula (n + 1) × Assignment D n) := AllDecisionWitness D z.2.1 z.2.2
  apply ((Name.atomicFamily_countable D small).union
    ((Set.countable_range decisions).union (Set.countable_range universals))).mono
  intro E hE
  rcases hE with atomic | (⟨n, φ, env, rfl⟩ | ⟨n, φ, env, rfl⟩)
  · exact Or.inl atomic
  · exact Or.inr (Or.inl ⟨⟨n, φ, env⟩, rfl⟩)
  · exact Or.inr (Or.inr ⟨⟨n, φ, env⟩, rfl⟩)

theorem exists_generic_formulaFamily (D : Name.NameDomain s) (small : D.names.Countable) (p : P) :
    ∃ H : ConditionFilter P, H.mem p ∧ H.GenericFor (formulaFamily D) :=
  exists_generic_for_countable_family p _ (formulaFamily_countable D small)

end PartitionPilot.Forcing.SetFormula

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



namespace PartitionPilot.Forcing

open SetRealization
universe u

namespace TransitiveGround

variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P)

theorem nameDomain_countable (small : M.sets.Countable) : (M.nameDomain s).names.Countable :=
  small.preimage Subtype.val_injective

theorem conditions_countable (small : M.sets.Countable) (carrier : s.carrier ∈ M.sets) :
    Countable P := by
  let : Countable M.sets := small
  let f : P → M.sets := fun p => ⟨s.encode p, M.transitive carrier (s.encode_mem p)⟩
  have injective : Function.Injective f := fun _ _ h => s.injective (congrArg Subtype.val h)
  exact injective.countable

end TransitiveGround
end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundCompleteProjectionGenericity
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

namespace SetFormula
variable {P : Type u} [Preorder P] [Countable P] {s : Presentation P}

theorem forces_iff_all_generics (D : Name.NameDomain s) (small : D.names.Countable)
    {n : Nat} (phi : SetFormula n) (env : Assignment D n) (p : P) :
    Forces D phi env p ↔
      ∀ H : ConditionFilter P, H.mem p → H.GenericFor (formulaFamily D) →
        Realize (D.values {q | H.mem q}) phi (evalAssignment {q | H.mem q} env) := by
  constructor
  · intro forced H member generic
    exact forces_sound D H generic phi env member forced
  · intro truth
    by_contra bad
    obtain ⟨q, below, negative⟩ := not_forces_refine_neg D phi env bad
    obtain ⟨H, member, generic⟩ := exists_generic_formulaFamily D small q
    have yes := truth H (H.upward member below) generic
    have no := forces_sound D H generic (.neg phi) env member negative
    exact no yes

end SetFormula

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem ordinaryForces_iff_all_generics (small : M.sets.Countable)
    (carrier : s.carrier ∈ M.sets) {n : Nat} (phi : SetFormula n)
    (env : Assignment (M.nameDomain s) n) (p : P) :
    Forces (M.nameDomain s) phi env p ↔
      ∀ H : ConditionFilter P, H.mem p → H.GenericFor (formulaFamily (M.nameDomain s)) →
        Realize ((M.nameDomain s).values {q | H.mem q}) phi
          (evalAssignment {q | H.mem q} env) := by
  let conditionsCountable : Countable P := M.conditions_countable s small carrier
  exact forces_iff_all_generics (M.nameDomain s) (M.nameDomain_countable s small) phi env p

end TransitiveGround
end



end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_StageOneDataBoundLaws
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

theorem stageOneAssignment_mem (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {t u w : ZFSet.{u}} (ht : t ∈ M.sets) (hu : u ∈ M.sets) (hw : w ∈ M.sets) :
    stageOneAssignment t u w ∈ M.sets :=
  M.orderedPair_mem pairing ht (M.orderedPair_mem pairing hu hw)

end TransitiveGround

open SetRealization
universe u

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
open SetRealization Compression.RecursiveMaps
universe u v
variable {P : Type u} [PartialOrder P] [OrderTop P] {s : Presentation P}

theorem eval_refinementClass (D : NameDomain s) (H : ConditionFilter P)
    (generic : H.GenericFor (atomicFamily D))
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (R w : Name s)
    (hR : R ∈ D.names)
    (pairs : ∀ z : Name s, z.val ∈ T → orderedPair ⊤ z w ∈ D.names) :
    eval {p | H.mem p} (refinementClass T valid R w) =
      equivalenceClass (eval {p | H.mem p} (familySet ⊤ T valid))
        (eval {p | H.mem p} R) (eval {p | H.mem p} w) := by
  apply ZFSet.ext
  intro x
  rw [mem_eval, mem_equivalenceClass]
  constructor
  · rintro ⟨z, p, entry, hp, rfl⟩
    obtain ⟨member, forced⟩ := (entry_refinementClass T valid R w z p).1 entry
    have related := forcesMem_sound D H generic (pairs z member) hR hp forced
    rw [eval_orderedPair {p | H.mem p} ⊤ H.top_mem z w] at related
    exact ⟨(mem_eval_familySet {p | H.mem p} ⊤ H.top_mem T valid _).2 ⟨z, member, rfl⟩, related⟩
  · rintro ⟨member, related⟩
    obtain ⟨z, hz, rfl⟩ := (mem_eval_familySet {p | H.mem p} ⊤ H.top_mem T valid x).1 member
    have named : eval {p | H.mem p} (orderedPair ⊤ z w) ∈ eval {p | H.mem p} R := by
      rw [eval_orderedPair {p | H.mem p} ⊤ H.top_mem z w]
      exact related
    obtain ⟨p, hp, forced⟩ := (eval_mem_iff_forcesMem D H generic (pairs z hz) hR).1 named
    exact ⟨z, p, (entry_refinementClass T valid R w z p).2 ⟨hz, forced⟩, hp, rfl⟩

end PartitionPilot.Forcing.Name



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] [OrderTop P]
variable (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)

include pairing carrier in
theorem eval_refinementClass {T : ZFSet.{u}} (hT : T ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (R w : Name s) (hR : R.val ∈ M.sets) (hw : w.val ∈ M.sets)
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily (M.nameDomain s))) :
    Name.eval {p | H.mem p} (Name.refinementClass T valid R w) =
      equivalenceClass (Name.eval {p | H.mem p} (Name.familySet ⊤ T valid))
        (Name.eval {p | H.mem p} R) (Name.eval {p | H.mem p} w) := by
  apply Name.eval_refinementClass (M.nameDomain s) H (fun E hE dense => generic E (Or.inl hE) dense)
    T valid R w hR
  intro z hz
  change (Name.orderedPair ⊤ z w).val ∈ M.sets
  rw [Name.orderedPair_code]
  exact M.orderedPairNameCode_mem pairing (M.transitive carrier (s.encode_mem ⊤))
    (M.transitive hT hz) hw

end TransitiveGround
end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_RefinementValidityCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

namespace BoundedFormula
open SetFormula

theorem truth_equivalenceRelationFormula {n} (S R : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (equivalenceRelationFormula S R) env ↔ EquivalenceRelationCode (env S) (env R) := by
  simp only [equivalenceRelationFormula, Truth, truth_relationBetweenFormula,
    truth_pairMembershipFormula, truth_imp]
  constructor
  · rintro ⟨shape, refl, symm, trans⟩
    refine ⟨shape, refl, ?_, ?_⟩
    · intro x y xy
      obtain ⟨hx, hy⟩ := ZFSet.pair_mem_prod.1 (shape xy)
      exact symm x hx y hy xy
    · intro x y z xy yz
      obtain ⟨hx, hy⟩ := ZFSet.pair_mem_prod.1 (shape xy)
      have hz := (ZFSet.pair_mem_prod.1 (shape yz)).2
      exact trans x hx y hy z hz ⟨xy, yz⟩
  · intro relation
    exact ⟨relation.shape, relation.refl,
      fun x _ y _ xy => relation.symm x y xy,
      fun x _ y _ z _ h => relation.trans x y z h.1 h.2⟩

theorem truth_refinementValidityFormula (env : Fin 4 → ZFSet.{u}) :
    Truth refinementValidityFormula env ↔
      RefinementValidityCode (env 3) (env 0) (env 1) (env 2) := by
  simp only [refinementValidityFormula, Truth, truth_subsetFormula,
    truth_equivalenceRelationFormula, RefinementValidityCode]

end BoundedFormula

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})

theorem realize_refinementValidityFormula (env : Fin 4 → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets BoundedFormula.refinementValidityFormula.toFormula env ↔
      RefinementValidityCode (env 3) (env 0) (env 1) (env 2) :=
  (BoundedFormula.realize_toFormula M _ _ members).trans
    (BoundedFormula.truth_refinementValidityFormula env)

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_ActiveNameImageSymmetry
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.Name
open SetRealization
universe u
variable {P : Type u} [Preorder P] {s : Presentation P}

theorem mem_eval_activeImage (D : NameDomain s) (H : ConditionFilter P)
    (generic : H.GenericFor (atomicFamily D))
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (U : Name s) (image : Name s → Name s) (hU : U ∈ D.names)
    (terms : ∀ w : Name s, w.val ∈ T → w ∈ D.names) (x : ZFSet.{u}) :
    x ∈ eval {p | H.mem p} (activeImage T valid U image) ↔
      ∃ w : Name s, w.val ∈ T ∧ eval {p | H.mem p} w ∈ eval {p | H.mem p} U ∧
        eval {p | H.mem p} (image w) = x := by
  rw [mem_eval]
  constructor
  · rintro ⟨σ, p, entry, hp, equal⟩
    obtain ⟨w, hw, forced, rfl⟩ := (entry_activeImage T valid U image σ p).1 entry
    exact ⟨w, hw, forcesMem_sound D H generic (terms w hw) hU hp forced, equal⟩
  · rintro ⟨w, hw, active, equal⟩
    obtain ⟨p, hp, forced⟩ := (eval_mem_iff_forcesMem D H generic (terms w hw) hU).1 active
    exact ⟨image w, p, (entry_activeImage T valid U image (image w) p).2
      ⟨w, hw, forced, rfl⟩, hp, equal⟩

end PartitionPilot.Forcing.Name



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_GroundRefinementQuotientNames
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

universe u

theorem refinementQuotientMap_subset (U Rf Rc : ZFSet.{u}) :
    refinementQuotientMap U Rf Rc ⊆
      ZFSet.prod (equivalenceClasses U Rf) (equivalenceClasses U Rc) := by
  intro z hz
  rw [refinementQuotientMap, relationCompose, ZFSet.mem_sep] at hz
  exact hz.1

theorem pair_mem_refinementQuotientMap (U Rf Rc C D : ZFSet.{u}) :
    ZFSet.pair C D ∈ refinementQuotientMap U Rf Rc ↔
      ∃ x ∈ U, C = equivalenceClass U Rf x ∧ D = equivalenceClass U Rc x := by
  rw [refinementQuotientMap, pair_mem_relationCompose]
  constructor
  · rintro ⟨_, _, x, hx, first, second⟩
    exact ⟨x, hx,
      ((pair_mem_equivalenceClassifier U Rf x C).1
        ((pair_mem_relationConverse _ _ _ x C).1 first).2.2).2,
      ((pair_mem_equivalenceClassifier U Rc x D).1 second).2⟩
  · rintro ⟨x, hx, rfl, rfl⟩
    have hf := equivalenceClass_mem (E := Rf) hx
    have hc := equivalenceClass_mem (E := Rc) hx
    exact ⟨hf, hc, x, hx, (pair_mem_relationConverse _ _ _ x _).2
      ⟨hx, hf, (pair_mem_equivalenceClassifier U Rf x _).2 ⟨hx, rfl⟩⟩,
      (pair_mem_equivalenceClassifier U Rc x _).2 ⟨hx, rfl⟩⟩

theorem mem_refinementQuotientMap (U Rf Rc z : ZFSet.{u}) :
    z ∈ refinementQuotientMap U Rf Rc ↔
      ∃ x ∈ U, z = ZFSet.pair (equivalenceClass U Rf x) (equivalenceClass U Rc x) := by
  constructor
  · intro hz
    obtain ⟨C, _, D, _, rfl⟩ := ZFSet.mem_prod.1 (refinementQuotientMap_subset U Rf Rc hz)
    obtain ⟨x, hx, rfl, rfl⟩ := (pair_mem_refinementQuotientMap U Rf Rc C D).1 hz
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact (pair_mem_refinementQuotientMap U Rf Rc _ _).2 ⟨x, hx, rfl, rfl⟩

theorem refinementQuotientMap_class_entry {U Rf Rc x : ZFSet.{u}} (hx : x ∈ U) :
    ZFSet.pair (equivalenceClass U Rf x) (equivalenceClass U Rc x) ∈
      refinementQuotientMap U Rf Rc :=
  (pair_mem_refinementQuotientMap U Rf Rc _ _).2 ⟨x, hx, rfl, rfl⟩

theorem refinementQuotientMap_value_iff {U Rf Rc x D : ZFSet.{u}}
    (fine : EquivalenceRelationCode U Rf) (coarse : EquivalenceRelationCode U Rc)
    (refinement : Rf ⊆ Rc) (hx : x ∈ U) :
    ZFSet.pair (equivalenceClass U Rf x) D ∈ refinementQuotientMap U Rf Rc ↔
      D = equivalenceClass U Rc x := by
  constructor
  · intro entry
    obtain ⟨y, hy, equal, rfl⟩ :=
      (pair_mem_refinementQuotientMap U Rf Rc _ D).1 entry
    exact ((coarse.class_eq_iff hx hy).2
      (refinement ((fine.class_eq_iff hx hy).1 equal))).symm
  · rintro rfl
    exact refinementQuotientMap_class_entry hx

theorem refinementQuotientMap_function {U Rf Rc : ZFSet.{u}}
    (fine : EquivalenceRelationCode U Rf) (coarse : EquivalenceRelationCode U Rc)
    (refinement : Rf ⊆ Rc) :
    ZFSet.IsFunc (equivalenceClasses U Rf) (equivalenceClasses U Rc)
      (refinementQuotientMap U Rf Rc) := by
  refine ⟨refinementQuotientMap_subset U Rf Rc, ?_⟩
  intro C hC
  obtain ⟨x, hx, rfl⟩ := (mem_equivalenceClasses U Rf C).1 hC
  exact ⟨equivalenceClass U Rc x, refinementQuotientMap_class_entry hx,
    fun D entry => (refinementQuotientMap_value_iff fine coarse refinement hx).1 entry⟩

theorem refinementQuotientMap_onto {U Rf Rc D : ZFSet.{u}}
    (hD : D ∈ equivalenceClasses U Rc) :
    ∃ C ∈ equivalenceClasses U Rf, ZFSet.pair C D ∈ refinementQuotientMap U Rf Rc := by
  obtain ⟨x, hx, rfl⟩ := (mem_equivalenceClasses U Rc D).1 hD
  exact ⟨equivalenceClass U Rf x, equivalenceClass_mem hx,
    refinementQuotientMap_class_entry hx⟩

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization
universe u

theorem equivalenceClass_eq_of_carrier_subset {T U R : ZFSet.{u}}
    (subset : U ⊆ T) (shape : R ⊆ ZFSet.prod U U) (x : ZFSet.{u}) :
    equivalenceClass T R x = equivalenceClass U R x := by
  apply ZFSet.ext
  intro y
  rw [mem_equivalenceClass, mem_equivalenceClass]
  exact ⟨fun h => ⟨(ZFSet.pair_mem_prod.1 (shape h.2)).1, h.2⟩,
    fun h => ⟨subset h.1, h.2⟩⟩

namespace Name
variable {P : Type u} [PartialOrder P] [OrderTop P] {s : Presentation P}

theorem eval_refinementQuotient (D : NameDomain s) (H : ConditionFilter P)
    (generic : H.GenericFor (atomicFamily D))
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (U R : Name s)
    (hU : U ∈ D.names) (hR : R ∈ D.names)
    (terms : ∀ w : Name s, w.val ∈ T → w ∈ D.names)
    (pairs : ∀ z w : Name s, z.val ∈ T → w.val ∈ T → orderedPair ⊤ z w ∈ D.names)
    (subset : eval {p | H.mem p} U ⊆ eval {p | H.mem p} (familySet ⊤ T valid))
    (shape : eval {p | H.mem p} R ⊆ ZFSet.prod (eval {p | H.mem p} U) (eval {p | H.mem p} U)) :
    eval {p | H.mem p} (refinementQuotient T valid U R) =
      equivalenceClasses (eval {p | H.mem p} U) (eval {p | H.mem p} R) := by
  have value (w : Name s) (hw : w.val ∈ T) :=
    (eval_refinementClass D H generic T valid R w hR (fun z hz => pairs z w hz hw)).trans
      (equivalenceClass_eq_of_carrier_subset subset shape (eval {p | H.mem p} w))
  apply ZFSet.ext
  intro C
  rw [refinementQuotient, mem_eval_activeImage D H generic T valid U _ hU terms,
    mem_equivalenceClasses]
  constructor
  · rintro ⟨w, hw, active, equal⟩
    exact ⟨eval {p | H.mem p} w, active, equal.symm.trans (value w hw)⟩
  · rintro ⟨x, hx, equal⟩
    obtain ⟨w, hw, rfl⟩ :=
      (mem_eval_familySet {p | H.mem p} ⊤ H.top_mem T valid x).1 (subset hx)
    exact ⟨w, hw, hx, (value w hw).trans equal.symm⟩

theorem eval_refinementNaturalMap (D : NameDomain s) (H : ConditionFilter P)
    (generic : H.GenericFor (atomicFamily D))
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (U Rf Rc : Name s)
    (hU : U ∈ D.names) (hRf : Rf ∈ D.names) (hRc : Rc ∈ D.names)
    (terms : ∀ w : Name s, w.val ∈ T → w ∈ D.names)
    (pairs : ∀ z w : Name s, z.val ∈ T → w.val ∈ T → orderedPair ⊤ z w ∈ D.names)
    (subset : eval {p | H.mem p} U ⊆ eval {p | H.mem p} (familySet ⊤ T valid))
    (fine : eval {p | H.mem p} Rf ⊆ ZFSet.prod (eval {p | H.mem p} U) (eval {p | H.mem p} U))
    (coarse : eval {p | H.mem p} Rc ⊆ ZFSet.prod (eval {p | H.mem p} U) (eval {p | H.mem p} U)) :
    eval {p | H.mem p} (refinementNaturalMap T valid U Rf Rc) =
      refinementQuotientMap (eval {p | H.mem p} U) (eval {p | H.mem p} Rf) (eval {p | H.mem p} Rc) := by
  have value (w : Name s) (hw : w.val ∈ T) :
      eval {p | H.mem p} (orderedPair ⊤ (refinementClass T valid Rf w) (refinementClass T valid Rc w)) =
      ZFSet.pair (equivalenceClass (eval {p | H.mem p} U) (eval {p | H.mem p} Rf) (eval {p | H.mem p} w))
        (equivalenceClass (eval {p | H.mem p} U) (eval {p | H.mem p} Rc) (eval {p | H.mem p} w)) := by
    rw [eval_orderedPair {p | H.mem p} ⊤ H.top_mem,
      eval_refinementClass D H generic T valid Rf w hRf (fun z hz => pairs z w hz hw),
      eval_refinementClass D H generic T valid Rc w hRc (fun z hz => pairs z w hz hw),
      equivalenceClass_eq_of_carrier_subset subset fine,
      equivalenceClass_eq_of_carrier_subset subset coarse]
  apply ZFSet.ext
  intro z
  rw [refinementNaturalMap, mem_eval_activeImage D H generic T valid U _ hU terms,
    mem_refinementQuotientMap]
  constructor
  · rintro ⟨w, hw, active, equal⟩
    exact ⟨eval {p | H.mem p} w, active, equal.symm.trans (value w hw)⟩
  · rintro ⟨x, hx, equal⟩
    obtain ⟨w, hw, rfl⟩ :=
      (mem_eval_familySet {p | H.mem p} ⊤ H.top_mem T valid x).1 (subset hx)
    exact ⟨w, hw, hx, (value w hw).trans equal.symm⟩

end Name

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRefinementValidityForcing
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

namespace TransitiveGround
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem refinementValidity_eval (env : Assignment (M.nameDomain s) 4)
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily (M.nameDomain s)))
    {p : P} (hp : H.mem p)
    (forced : Forces (M.nameDomain s) BoundedFormula.refinementValidityFormula.toFormula env p) :
    RefinementValidityCode
      (Name.eval {q | H.mem q} (env 3).val) (Name.eval {q | H.mem q} (env 0).val)
      (Name.eval {q | H.mem q} (env 1).val) (Name.eval {q | H.mem q} (env 2).val) := by
  let evaluated : TransitiveGround.{u} :=
    ⟨(M.nameDomain s).values {q | H.mem q}, (M.nameDomain s).values_transitive {q | H.mem q}⟩
  have truth := forces_sound (M.nameDomain s) H generic _ env hp forced
  exact (evaluated.realize_refinementValidityFormula
    (evalAssignment {q | H.mem q} env) (fun j => ⟨env j, rfl⟩)).1 truth

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundNormalizedRefinementOutputs
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

theorem equivalenceClass_empty_of_not_mem {U R x : ZFSet.{u}}
    (shape : R ⊆ ZFSet.prod U U) (inactive : x ∉ U) : equivalenceClass U R x = ∅ := by
  apply ZFSet.ext
  intro y
  constructor
  · intro hy
    exact False.elim (inactive (ZFSet.pair_mem_prod.1 (shape (mem_equivalenceClass U R x y |>.1 hy).2)).2)
  · exact False.elim ∘ ZFSet.notMem_empty y

namespace TransitiveGround
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] [OrderTop P] (s : Presentation P)

theorem refinementObjects_eval
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0) (carrier : s.carrier ∈ M.sets)
    {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
    (hFamily : (Name.familySet ⊤ T valid).val ∈ M.sets)
    (U Rf Rc : (M.nameDomain s).names)
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily (M.nameDomain s)))
    {p : P} (hp : H.mem p)
    (forced : Forces (M.nameDomain s) BoundedFormula.refinementValidityFormula.toFormula
      (M.refinementNameEnv s T valid hFamily U Rf Rc) p) :
    RefinementObjectValues {q | H.mem q} T valid U.val Rf.val Rc.val := by
  have validity : RefinementValidityCode (Name.eval {q | H.mem q} (Name.familySet ⊤ T valid))
      (Name.eval {q | H.mem q} U.val) (Name.eval {q | H.mem q} Rf.val) (Name.eval {q | H.mem q} Rc.val) :=
    M.refinementValidity_eval s (M.refinementNameEnv s T valid hFamily U Rf Rc) H generic hp forced
  have atomic : H.GenericFor (Name.atomicFamily (M.nameDomain s)) :=
    fun E hE dense => generic E (Or.inl hE) dense
  have terms (w : Name s) (hw : w.val ∈ T) : w ∈ (M.nameDomain s).names := M.transitive hT hw
  have pairs (z w : Name s) (hz : z.val ∈ T) (hw : w.val ∈ T) :
      Name.orderedPair ⊤ z w ∈ (M.nameDomain s).names := by
    change (Name.orderedPair ⊤ z w).val ∈ M.sets
    rw [Name.orderedPair_code]
    exact M.orderedPairNameCode_mem pairing (M.transitive carrier (s.encode_mem ⊤))
      (M.transitive hT hz) (M.transitive hT hw)
  have fineClass (w : Name s) (hw : w.val ∈ T) :=
    (M.eval_refinementClass s pairing carrier hT valid Rf.val w Rf.property (M.transitive hT hw) H generic).trans
      (equivalenceClass_eq_of_carrier_subset validity.1 validity.2.1.shape (Name.eval {q | H.mem q} w))
  have coarseClass (w : Name s) (hw : w.val ∈ T) :=
    (M.eval_refinementClass s pairing carrier hT valid Rc.val w Rc.property (M.transitive hT hw) H generic).trans
      (equivalenceClass_eq_of_carrier_subset validity.1 validity.2.2.1.shape (Name.eval {q | H.mem q} w))
  have fineQuotient := Name.eval_refinementQuotient (M.nameDomain s) H atomic T valid U.val Rf.val
    U.property Rf.property terms pairs validity.1 validity.2.1.shape
  have coarseQuotient := Name.eval_refinementQuotient (M.nameDomain s) H atomic T valid U.val Rc.val
    U.property Rc.property terms pairs validity.1 validity.2.2.1.shape
  have naturalMap := Name.eval_refinementNaturalMap (M.nameDomain s) H atomic T valid U.val Rf.val Rc.val
    U.property Rf.property Rc.property terms pairs validity.1 validity.2.1.shape validity.2.2.1.shape
  refine ⟨validity, fineClass, coarseClass, fineQuotient, coarseQuotient, naturalMap, ?_, ?_, ?_⟩
  · rw [fineQuotient, coarseQuotient, naturalMap]
    exact refinementQuotientMap_function validity.2.1 validity.2.2.1 validity.2.2.2
  · intro C hC
    rw [coarseQuotient] at hC
    obtain ⟨D, hD, entry⟩ := refinementQuotientMap_onto (Rf := Name.eval {q | H.mem q} Rf.val) hC
    exact ⟨D, fineQuotient.symm ▸ hD, naturalMap.symm ▸ entry⟩
  · intro w hw inactive
    rw [fineClass w hw, coarseClass w hw]
    exact ⟨equivalenceClass_empty_of_not_mem validity.2.1.shape inactive,
      equivalenceClass_empty_of_not_mem validity.2.2.1.shape inactive⟩

end TransitiveGround

end PartitionPilot.Forcing



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRenamedNameFamilyBounds
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L)
variable (d : PosetAction G L) (base : L)
variable (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (T : ZFSet.{u}) (H : ConditionFilter P)

theorem encode_mem_visibleSupportProfile (z : ZFSet.{u}) (v : L) :
    b.encode v ∈ M.visibleSupportProfile a s b d T H z ↔
      z ∈ Name.eval {p | H.mem p} (M.niceVisibilityName a s T (d.principalFix v)) :=
  b.encode_mem_subset _ v

theorem visibleSupportProfile_upward (z : ZFSet.{u}) {v w : L} (lower : v ≤ w)
    (member : b.encode v ∈ M.visibleSupportProfile a s b d T H z) :
    b.encode w ∈ M.visibleSupportProfile a s b d T H z := by
  have seen := (M.encode_mem_visibleSupportProfile a s b d T H z v).1 member
  obtain ⟨τ, candidate, equal⟩ :=
    (M.mem_eval_niceVisibilityName a s T (d.principalFix v) _ H.top_mem z).1 seen
  have data := (M.name_mem_niceNameCandidates a s T (d.principalFix v) τ).1 candidate
  apply (M.encode_mem_visibleSupportProfile a s b d T H z w).2
  apply (M.mem_eval_niceVisibilityName a s T (d.principalFix w) _ H.top_mem z).2
  exact ⟨τ, (M.name_mem_niceNameCandidates a s T (d.principalFix w) τ).2
    ⟨data.1, data.2.1, le_trans (d.principalFix_antitone lower) data.2.2⟩, equal⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_RefinementCoarseImageNames
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u v

theorem mem_coarseClassImage (U sigma Rc z : ZFSet.{u}) :
    z ∈ coarseClassImage U sigma Rc ↔
      z ∈ U ∧ ∃ y ∈ sigma, y ∈ U ∧ ZFSet.pair z y ∈ Rc := ZFSet.mem_sep

theorem coarseClassImage_of_fineClass {U Rf Rc x : ZFSet.{u}}
    (fine : EquivalenceRelationCode U Rf) (coarse : EquivalenceRelationCode U Rc)
    (refinement : Rf ⊆ Rc) (hx : x ∈ U) :
    coarseClassImage U (equivalenceClass U Rf x) Rc = equivalenceClass U Rc x := by
  apply ZFSet.ext
  intro z
  rw [mem_coarseClassImage, mem_equivalenceClass]
  constructor
  · rintro ⟨hz, y, hy, _, related⟩
    exact ⟨hz, coarse.trans z y x related (refinement ((mem_equivalenceClass U Rf x y).1 hy).2)⟩
  · rintro ⟨hz, related⟩
    exact ⟨hz, x, fine.class_self hx, hx, related⟩

namespace BoundedFormula

theorem truth_coarseClassImageFormula (env : Fin 4 → ZFSet.{u}) :
    Truth coarseClassImageFormula env ↔ env 0 ∈ coarseClassImage (env 1) (env 2) (env 3) := by
  rw [mem_coarseClassImage]
  change (env 0 ∈ env 1 ∧ Truth (exMem 2 (.conj (.mem 0 2) (pairMembershipFormula 1 0 4))) env) ↔ _
  rw [truth_exMem]
  exact and_congr_right (fun _ => exists_congr (fun y => and_congr_right (fun _ =>
    and_congr_right (fun _ => truth_pairMembershipFormula 1 0 4 (extend y env)))))

end BoundedFormula

namespace Name
variable {P : Type u} [PartialOrder P] [OrderTop P] {s : Presentation P}

theorem eval_refinementCoarseImage (D : NameDomain s) (T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) (U sigma Rc : D.names)
    (family : familySet ⊤ T valid ∈ D.names) (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily D)) :
    eval {p | H.mem p} (refinementCoarseImage D T valid U sigma Rc) =
      coarseClassImage (eval {p | H.mem p} U.val) (eval {p | H.mem p} sigma.val)
        (eval {p | H.mem p} Rc.val) ∩ eval {p | H.mem p} (familySet ⊤ T valid) := by
  rw [refinementCoarseImage, eval_separationName D H generic _ _ family]
  let evaluated : TransitiveGround.{u} := ⟨D.values {p | H.mem p}, D.values_transitive _⟩
  apply ZFSet.ext
  intro x
  rw [ZFSet.mem_sep, ZFSet.mem_inter]
  constructor
  · rintro ⟨hx, formula⟩
    have members : ∀ j, extend x (evalAssignment {p | H.mem p}
        (extend U (extend sigma (extend Rc Fin.elim0)))) j ∈ D.values {p | H.mem p} :=
      Fin.cases ((D.values_transitive _ (show eval {p | H.mem p} (familySet ⊤ T valid) ∈ D.values {p | H.mem p} from ⟨⟨_, family⟩, rfl⟩)) hx)
        (fun j => ⟨(extend U (extend sigma (extend Rc Fin.elim0))) j, rfl⟩)
    have truth := (BoundedFormula.realize_toFormula evaluated BoundedFormula.coarseClassImageFormula _ members).1 formula
    exact ⟨(BoundedFormula.truth_coarseClassImageFormula _).1 truth, hx⟩
  · rintro ⟨member, hx⟩
    have members : ∀ j, extend x (evalAssignment {p | H.mem p}
        (extend U (extend sigma (extend Rc Fin.elim0)))) j ∈ D.values {p | H.mem p} :=
      Fin.cases ((D.values_transitive _ (show eval {p | H.mem p} (familySet ⊤ T valid) ∈ D.values {p | H.mem p} from ⟨⟨_, family⟩, rfl⟩)) hx)
        (fun j => ⟨(extend U (extend sigma (extend Rc Fin.elim0))) j, rfl⟩)
    exact ⟨hx, (BoundedFormula.realize_toFormula evaluated BoundedFormula.coarseClassImageFormula _ members).2
      ((BoundedFormula.truth_coarseClassImageFormula (extend x (evalAssignment {p | H.mem p}
        (extend U (extend sigma (extend Rc Fin.elim0)))))).2 member)⟩

theorem eval_refinementCoarseImage_of_subset (D : NameDomain s) (T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) (U sigma Rc : D.names)
    (family : familySet ⊤ T valid ∈ D.names) (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily D))
    (subset : eval {p | H.mem p} U.val ⊆ eval {p | H.mem p} (familySet ⊤ T valid)) :
    eval {p | H.mem p} (refinementCoarseImage D T valid U sigma Rc) =
      coarseClassImage (eval {p | H.mem p} U.val) (eval {p | H.mem p} sigma.val)
        (eval {p | H.mem p} Rc.val) := by
  rw [eval_refinementCoarseImage D T valid U sigma Rc family H generic]
  apply ZFSet.ext
  intro x
  exact ⟨fun h => (ZFSet.mem_inter.1 h).1,
    fun h => ZFSet.mem_inter.2 ⟨h, subset ((mem_coarseClassImage _ _ _ _).1 h).1⟩⟩

variable {G : Type v} [Group G] (a : PosetAction G P)

theorem refinementCoarseImage_support (D : NameDomain s)
    (closed : ∀ g z, z ∈ D.names → a.act s g z ∈ D.names)
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (terms : ∀ g (z : Name s), z.val ∈ T → (a.act s g z).val ∈ T)
    (U sigma Rc : D.names) (K : Subgroup G)
    (domain : K ≤ a.stabilizer s U.val) (witness : K ≤ a.stabilizer s sigma.val)
    (relation : K ≤ a.stabilizer s Rc.val) :
    K ≤ a.stabilizer s (refinementCoarseImage D T valid U sigma Rc) := by
  intro g hg
  change a.act s g (refinementCoarseImage D T valid U sigma Rc) = _
  unfold refinementCoarseImage
  rw [a.act_separationName s D closed, act_familySet a T valid terms]
  have env : a.actAssignment s D closed g (extend U (extend sigma (extend Rc Fin.elim0))) =
      extend U (extend sigma (extend Rc Fin.elim0)) := by
    funext j
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))) j
    · exact Subtype.ext (domain hg)
    · exact Subtype.ext (witness hg)
    · exact Subtype.ext (relation hg)
  rw [env]

end Name

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundRefinementCoarseVisibility
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
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)

include pairing unions powers separation collection carrier order in
theorem refinementCoarseImage_mem {T : ZFSet.{u}} (hT : T ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (U sigma Rc : (M.nameDomain s).names) :
    (Name.refinementCoarseImage (M.nameDomain s) T valid U sigma Rc).val ∈ M.sets :=
  M.ordinarySeparationName_mem s pairing unions powers separation collection carrier order
    BoundedFormula.coarseClassImageFormula.toFormula (extend U (extend sigma (extend Rc Fin.elim0)))
    ⟨Name.familySet ⊤ T valid, M.familySet_mem s ⊤ pairing unions powers separation hT
      (M.transitive carrier (s.encode_mem ⊤)) valid⟩

variable (a : PosetAction G P) (t : Presentation G)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable (b : Presentation L) (d : PosetAction G L) (base : L)
variable (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
variable (terms : ∀ g (z : Name s), z.val ∈ T → (a.act s g z).val ∈ T)

include pairing unions powers separation collection carrier maps terms in
theorem refinementCoarseImage_principal_support (U sigma Rc : (M.nameDomain s).names)
    {C v : L} (lower : C ≤ v)
    (domain : d.principalFix C ≤ a.stabilizer s U.val)
    (witness : d.principalFix v ≤ a.stabilizer s sigma.val)
    (relation : d.principalFix C ≤ a.stabilizer s Rc.val) :
    d.principalFix v ≤ a.stabilizer s (Name.refinementCoarseImage (M.nameDomain s) T valid U sigma Rc) :=
  Name.refinementCoarseImage_support a (M.nameDomain s)
    (fun g z hz => M.act_mem s a t pairing unions powers separation collection carrier maps g z hz)
    T valid terms U sigma Rc (d.principalFix v)
    (le_trans (d.principalFix_antitone lower) domain) witness
    (le_trans (d.principalFix_antitone lower) relation)

include pairing unions powers separation collection carrier order maps hT terms in
theorem coarseClass_visible_of_fineValue
    (system : NiceNameSystem M a s b d base directed T valid)
    (U sigma Rf Rc : (M.nameDomain s).names) {C v : L} (lower : C ≤ v)
    (domain : d.principalFix C ≤ a.stabilizer s U.val)
    (witness : d.principalFix v ≤ a.stabilizer s sigma.val)
    (relation : d.principalFix C ≤ a.stabilizer s Rc.val)
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily (M.nameDomain s)))
    (validity : RefinementValidityCode (Name.eval {p | H.mem p} (Name.familySet ⊤ T valid))
      (Name.eval {p | H.mem p} U.val) (Name.eval {p | H.mem p} Rf.val) (Name.eval {p | H.mem p} Rc.val))
    {x : ZFSet.{u}} (hx : x ∈ Name.eval {p | H.mem p} U.val)
    (fineValue : Name.eval {p | H.mem p} sigma.val =
      equivalenceClass (Name.eval {p | H.mem p} U.val) (Name.eval {p | H.mem p} Rf.val) x) :
    equivalenceClass (Name.eval {p | H.mem p} U.val) (Name.eval {p | H.mem p} Rc.val) x ∈
      Name.eval {p | H.mem p} (M.niceVisibilityName a s T (d.principalFix v)) := by
  let image : (M.nameDomain s).names :=
    ⟨Name.refinementCoarseImage (M.nameDomain s) T valid U sigma Rc,
      M.refinementCoarseImage_mem s pairing unions powers separation collection carrier order hT valid U sigma Rc⟩
  have support := M.refinementCoarseImage_principal_support s pairing unions powers separation collection
    carrier a t maps d valid terms U sigma Rc lower domain witness relation
  have family := M.familySet_mem s ⊤ pairing unions powers separation hT
    (M.transitive carrier (s.encode_mem ⊤)) valid
  have value : Name.eval {p | H.mem p} image.val =
      equivalenceClass (Name.eval {p | H.mem p} U.val) (Name.eval {p | H.mem p} Rc.val) x := by
    change Name.eval {p | H.mem p} (Name.refinementCoarseImage (M.nameDomain s) T valid U sigma Rc) = _
    rw [Name.eval_refinementCoarseImage_of_subset (M.nameDomain s) T valid U sigma Rc family H generic validity.1,
      fineValue, coarseClassImage_of_fineClass validity.2.1 validity.2.2.1 validity.2.2.2 hx]
  have subset : Name.eval {p | H.mem p} image.val ⊆
      Name.eval {p | H.mem p} (Name.familySet ⊤ T valid) := by
    rw [value]
    exact fun _ h => validity.1 (equivalenceClass_subset _ _ _ h)
  exact value ▸ system.normalization_visible v image support H generic subset

include pairing unions powers separation collection carrier order maps hT terms in
theorem refinementQuotientMap_preserves_visibility
    (system : NiceNameSystem M a s b d base directed T valid)
    (U Rf Rc : (M.nameDomain s).names) {C v : L} (lower : C ≤ v)
    (domain : d.principalFix C ≤ a.stabilizer s U.val)
    (relation : d.principalFix C ≤ a.stabilizer s Rc.val)
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily (M.nameDomain s)))
    (validity : RefinementValidityCode (Name.eval {p | H.mem p} (Name.familySet ⊤ T valid))
      (Name.eval {p | H.mem p} U.val) (Name.eval {p | H.mem p} Rf.val) (Name.eval {p | H.mem p} Rc.val))
    {fineClass coarseClass : ZFSet.{u}}
    (visible : fineClass ∈ Name.eval {p | H.mem p} (M.niceVisibilityName a s T (d.principalFix v)))
    (entry : ZFSet.pair fineClass coarseClass ∈ refinementQuotientMap
      (Name.eval {p | H.mem p} U.val) (Name.eval {p | H.mem p} Rf.val) (Name.eval {p | H.mem p} Rc.val)) :
    coarseClass ∈ Name.eval {p | H.mem p} (M.niceVisibilityName a s T (d.principalFix v)) := by
  obtain ⟨sigma, candidate, value⟩ :=
    (M.mem_eval_niceVisibilityName a s T (d.principalFix v) {p | H.mem p} H.top_mem fineClass).1 visible
  have hsigma := (M.name_mem_niceNameCandidates a s T (d.principalFix v) sigma).1 candidate
  obtain ⟨x, hx, fineValue, coarseValue⟩ := (pair_mem_refinementQuotientMap _ _ _ _ _).1 entry
  rw [coarseValue]
  exact M.coarseClass_visible_of_fineValue s pairing unions powers separation collection carrier order
    a t maps b d base directed hT valid terms system U ⟨sigma, hsigma.1⟩ Rf Rc lower domain hsigma.2.2
    relation H generic validity hx (value.trans fineValue)

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundNiceRefinementVisibility
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]

theorem niceRefinementIndex_preserves_visibility
    (s : Presentation P)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (a : PosetAction G P) (t : Presentation G) (maps : a.conditionMapFamily s t ∈ M.sets)
    (b : Presentation L) (d : PosetAction G L) (base : L)
    (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    {level T1 T2 : ZFSet.{u}} (hT1 : T1 ∈ M.sets)
    {valid1 : ∀ z ∈ T1, IsName s z} {valid2 : ∀ z ∈ T2, IsName s z}
    (terms : ∀ g (z : Name s), z.val ∈ T1 → (a.act s g z).val ∈ T1)
    (system : NiceNameSystem M a s b d base directed T1 valid1)
    (indices : NiceRefinementIndexSystem M a s b d level T1 T2 valid1 valid2)
    (C E : L) (U Rf Rc : (M.nameDomain s).names)
    (member : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d level T1 T2 valid1)
    {v : L} (lower : C ≤ v)
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily (M.nameDomain s)))
    {fineClass coarseClass : ZFSet.{u}}
    (visible : fineClass ∈ Name.eval {p | H.mem p} (M.niceVisibilityName a s T1 (d.principalFix v)))
    (entry : ZFSet.pair fineClass coarseClass ∈
      Name.eval {p | H.mem p} (Name.refinementNaturalMap T1 valid1 U.val Rf.val Rc.val)) :
    coarseClass ∈ Name.eval {p | H.mem p} (M.niceVisibilityName a s T1 (d.principalFix v)) := by
  obtain ⟨_, hU, _, hRc, forced⟩ := (indices.typed_entries C E U Rf Rc).1 member
  have domain := ((M.name_mem_niceNameCandidates a s T1 (d.principalFix C) U.val).1 hU).2.2
  have relation := ((M.name_mem_niceNameCandidates a s T2 (d.principalFix C) Rc.val).1 hRc).2.2
  have values := M.refinementObjects_eval s pairing carrier hT1 valid1 indices.family_ground
    U Rf Rc H generic H.top_mem forced
  rw [values.natural_map] at entry
  exact M.refinementQuotientMap_preserves_visibility s pairing unions powers separation collection
    carrier order a t maps b d base directed hT1 valid1 terms system U Rf Rc lower domain relation
    H generic values.validity visible entry

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundStageOneAssignmentUnions
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

theorem truth_refinementCollisionFormula (env : Fin 4 → ZFSet.{u}) :
    Truth refinementCollisionFormula env ↔ (env 0 = env 1 ↔ env 2 = env 3) := by
  simp only [refinementCollisionFormula, Truth, truth_imp]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩

theorem truth_refinementProfileFormula (env : Fin 3 → ZFSet.{u}) :
    Truth refinementProfileFormula env ↔ (env 0 ∈ env 2 ↔ env 1 ∈ env 2) := by
  simp only [refinementProfileFormula, Truth, truth_imp]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩

theorem truth_refinementCompatibilityFormula (env : Fin 4 → ZFSet.{u}) :
    Truth refinementCompatibilityFormula env ↔
      (env 0 ∈ env 1 → ZFSet.pair (env 0) (env 2) ∈ env 3) := by
  rw [refinementCompatibilityFormula, truth_imp, truth_pairMembershipFormula]
  rfl

end BoundedFormula
namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})

theorem realize_refinementCollisionFormula (env : Fin 4 → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets refinementCollisionFormula env ↔ (env 0 = env 1 ↔ env 2 = env 3) :=
  (BoundedFormula.realize_toFormula M _ _ members).trans
    (BoundedFormula.truth_refinementCollisionFormula env)

theorem realize_refinementProfileFormula (env : Fin 3 → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets refinementProfileFormula env ↔ (env 0 ∈ env 2 ↔ env 1 ∈ env 2) :=
  (BoundedFormula.realize_toFormula M _ _ members).trans
    (BoundedFormula.truth_refinementProfileFormula env)

theorem realize_refinementCompatibilityFormula (env : Fin 4 → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets refinementCompatibilityFormula env ↔
      (env 0 ∈ env 1 → ZFSet.pair (env 0) (env 2) ∈ env 3) :=
  (BoundedFormula.realize_toFormula M _ _ members).trans
    (BoundedFormula.truth_refinementCompatibilityFormula env)

end TransitiveGround
end

namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem refinementCompatibility_eval (env : Assignment (M.nameDomain s) 4)
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily (M.nameDomain s)))
    {p : P} (hp : H.mem p)
    (forced : Forces (M.nameDomain s) refinementCompatibilityFormula env p) :
    Name.eval {q | H.mem q} (env 0).val ∈ Name.eval {q | H.mem q} (env 1).val →
      ZFSet.pair (Name.eval {q | H.mem q} (env 0).val)
        (Name.eval {q | H.mem q} (env 2).val) ∈ Name.eval {q | H.mem q} (env 3).val := by
  let evaluated : TransitiveGround.{u} :=
    ⟨(M.nameDomain s).values {q | H.mem q}, (M.nameDomain s).values_transitive {q | H.mem q}⟩
  exact (evaluated.realize_refinementCompatibilityFormula (evalAssignment {q | H.mem q} env)
    (fun j => ⟨env j, rfl⟩)).1
      (forces_sound (M.nameDomain s) H generic _ env hp forced)

end TransitiveGround

open SetRealization SetFormula
universe u

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
variable (M : TransitiveGround.{u}) (d : Fin 15 → ZFSet.{u})

theorem stageOneRawTests_cut_iff (levels beta A lower : ZFSet.{u})
    (covered : ∀ t ∈ d 0, ∀ u ∈ d 6, ∀ w ∈ d 6,
      ∃ xi ∈ beta, ZFSet.pair (stageOneAssignment t u w) xi ∈ levels) :
    stageOneRawTests M d (assignmentCut levels beta A) lower ↔ stageOneRawTests M d A lower := by
  apply stageOneRawTests_congr
  intro t ht u hu w hw
  rw [mem_assignmentCut]
  exact ⟨And.left, fun entry => ⟨entry, covered t ht u hu w hw⟩⟩

theorem stageTwoConditionCode_cut_iff (levels alpha beta row A : ZFSet.{u})
    (below : alpha ⊆ beta)
    (covered : ∀ t ∈ d 0, ∀ u ∈ d 6, ∀ w ∈ d 6,
      ∃ xi ∈ beta, ZFSet.pair (stageOneAssignment t u w) xi ∈ levels) :
    StageTwoConditionCode M levels alpha d (ZFSet.pair row (assignmentCut levels beta A)) ↔
      StageTwoConditionCode M levels alpha d (ZFSet.pair row A) := by
  rw [stageTwoConditionCode_pair_iff, stageTwoConditionCode_pair_iff, assignmentCut_nested below]
  exact and_congr Iff.rfl (stageOneRawTests_cut_iff M d levels beta A _ covered)

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_ForcingHistoryTestDecomposition
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
universe u

theorem forcingHistoryConditionCode_insert_iff {M : TransitiveGround.{u}}
    {stages history levels alpha data z : ZFSet.{u}}
    (function : FunctionGraphOn stages history) (outside : alpha ∉ stages) :
    ForcingHistoryConditionCode M (insert alpha stages)
      (insert (ZFSet.pair alpha data) history) levels z ↔
      ForcingHistoryConditionCode M stages history levels z ∧
        PackedSuccessorConditionCode M levels alpha data z := by
  constructor
  · intro valid
    constructor
    · intro beta member
      obtain ⟨value, entry, checked⟩ := valid beta (ZFSet.mem_insert_of_mem alpha member)
      rcases ZFSet.mem_insert_iff.1 entry with equal | old
      · have same := (ZFSet.pair_inj.1 equal).1
        exact False.elim (outside (same ▸ member))
      · exact ⟨value, old, checked⟩
    · obtain ⟨value, entry, checked⟩ := valid alpha (ZFSet.mem_insert alpha stages)
      have same := (function.insert outside data).unique entry (ZFSet.mem_insert _ _)
      exact same ▸ checked
  · rintro ⟨prior, current⟩ beta member
    rcases ZFSet.mem_insert_iff.1 member with rfl | member
    · exact ⟨data, ZFSet.mem_insert _ _, current⟩
    · obtain ⟨value, entry, checked⟩ := prior beta member
      exact ⟨value, ZFSet.mem_insert_of_mem _ entry, checked⟩

theorem stageTwoConditionCode_levels_congr (M : TransitiveGround.{u})
    (d : Fin 15 → ZFSet.{u}) (first second alpha z : ZFSet.{u})
    (cuts : ∀ A, assignmentCut first alpha A = assignmentCut second alpha A) :
    StageTwoConditionCode M first alpha d z ↔ StageTwoConditionCode M second alpha d z := by
  constructor
  · rintro ⟨row, A, equal, member, tests⟩
    rw [cuts A] at member tests
    exact ⟨row, A, equal, member, tests⟩
  · rintro ⟨row, A, equal, member, tests⟩
    rw [← cuts A] at member tests
    exact ⟨row, A, equal, member, tests⟩

theorem packedSuccessorConditionCode_levels_congr (M : TransitiveGround.{u})
    (first second alpha data z : ZFSet.{u})
    (cuts : ∀ A, assignmentCut first alpha A = assignmentCut second alpha A) :
    PackedSuccessorConditionCode M first alpha data z ↔
      PackedSuccessorConditionCode M second alpha data z := by
  constructor
  · rintro ⟨d, equal, checked⟩
    exact ⟨d, equal, (stageTwoConditionCode_levels_congr M d first second alpha z cuts).1 checked⟩
  · rintro ⟨d, equal, checked⟩
    exact ⟨d, equal, (stageTwoConditionCode_levels_congr M d first second alpha z cuts).2 checked⟩

theorem forcingHistoryConditionCode_levels_congr (M : TransitiveGround.{u})
    (stages history first second z : ZFSet.{u})
    (cuts : ∀ alpha ∈ stages, ∀ A, assignmentCut first alpha A = assignmentCut second alpha A) :
    ForcingHistoryConditionCode M stages history first z ↔
      ForcingHistoryConditionCode M stages history second z := by
  constructor
  · intro valid alpha member
    obtain ⟨data, entry, checked⟩ := valid alpha member
    exact ⟨data, entry, (packedSuccessorConditionCode_levels_congr M first second alpha data z
      (cuts alpha member)).1 checked⟩
  · intro valid alpha member
    obtain ⟨data, entry, checked⟩ := valid alpha member
    exact ⟨data, entry, (packedSuccessorConditionCode_levels_congr M first second alpha data z
      (cuts alpha member)).2 checked⟩

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem forcingHistoryConditionCode_cut_iff (M : TransitiveGround.{u})
    (stages history levels alpha row A : ZFSet.{u})
    (below : ∀ beta ∈ stages, beta ⊆ alpha)
    (covered : ∀ beta ∈ stages, ∀ d : Fin 15 → ZFSet.{u},
      ZFSet.pair beta (refinementFormulaDataCode d) ∈ history →
        ∀ t ∈ d 0, ∀ u ∈ d 6, ∀ w ∈ d 6,
          ∃ xi ∈ alpha, ZFSet.pair (stageOneAssignment t u w) xi ∈ levels) :
    ForcingHistoryConditionCode M stages history levels (ZFSet.pair row (assignmentCut levels alpha A)) ↔
      ForcingHistoryConditionCode M stages history levels (ZFSet.pair row A) := by
  constructor
  · intro valid beta member
    obtain ⟨data, entry, d, equal, tests⟩ := valid beta member
    rw [equal] at entry
    refine ⟨refinementFormulaDataCode d, entry, d, rfl, ?_⟩
    exact (stageTwoConditionCode_cut_iff M d levels beta alpha row A (below beta member)
      (covered beta member d entry)).1 tests
  · intro valid beta member
    obtain ⟨data, entry, d, equal, tests⟩ := valid beta member
    rw [equal] at entry
    refine ⟨refinementFormulaDataCode d, entry, d, rfl, ?_⟩
    exact (stageTwoConditionCode_cut_iff M d levels beta alpha row A (below beta member)
      (covered beta member d entry)).2 tests

theorem forcingHistoryConditionCode_ordinalCut_iff (M : TransitiveGround.{u})
    (stages history levels alpha row A : ZFSet.{u})
    (ordinal : ordinalSetProperty alpha) (subset : stages ⊆ alpha)
    (coverage : ForcingHistoryLevelCoverage stages history levels) :
    ForcingHistoryConditionCode M stages history levels (ZFSet.pair row (assignmentCut levels alpha A)) ↔
      ForcingHistoryConditionCode M stages history levels (ZFSet.pair row A) := by
  apply forcingHistoryConditionCode_cut_iff M stages history levels alpha row A
  · intro beta member xi hxi
    exact ordinal.1 beta (subset member) xi hxi
  · intro beta member d entry t ht u hu w hw
    exact ⟨beta, subset member, coverage beta member d entry t ht u hu w hw⟩

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundForcingHistorySuccessors
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround

section
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem mem_stageTwoConditions (rawRowCarrier I levels alpha : ZFSet.{u})
    (d : Fin 15 → ZFSet.{u}) (z : ZFSet.{u}) :
    z ∈ M.stageTwoConditions rawRowCarrier I levels alpha d ↔
      z ∈ M.stageOneCandidateBound rawRowCarrier I (d 6) ∧
        StageTwoConditionCode M levels alpha d z := ZFSet.mem_sep

theorem pair_mem_stageTwoConditions (rawRowCarrier I levels alpha : ZFSet.{u})
    (d : Fin 15 → ZFSet.{u}) (row A : ZFSet.{u}) :
    ZFSet.pair row A ∈ M.stageTwoConditions rawRowCarrier I levels alpha d ↔
      row ∈ rawRowCarrier ∧ A ∈ M.sets ∧ A ⊆ stageOneAssignments I (d 6) ∧
        M.groundEmbeddable A ZFSet.omega ∧
        ZFSet.pair row (assignmentCut levels alpha A) ∈ d 7 ∧
        stageOneRawTests M d A (ZFSet.pair row (assignmentCut levels alpha A)) := by
  rw [M.mem_stageTwoConditions, M.pair_mem_stageOneCandidateBound]
  constructor
  · rintro ⟨⟨hr, hA, subset, small⟩, row', A', equal, lower, tests⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_injective equal
    exact ⟨hr, hA, subset, small, lower, tests⟩
  · rintro ⟨hr, hA, subset, small, lower, tests⟩
    exact ⟨⟨hr, hA, subset, small⟩, row, A, rfl, lower, tests⟩

end

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem forcingHistoryConditions_successor_eq
    (rows oldI I alpha history levels : ZFSet.{u}) (d : Fin 15 → ZFSet.{u})
    (function : FunctionGraphOn alpha history) (ordinal : ordinalSetProperty alpha)
    (coverage : ForcingHistoryLevelCoverage alpha history levels)
    (lower : d 7 = M.forcingHistoryConditions rows oldI (d 6) alpha history levels) :
    M.forcingHistoryConditions rows I (d 6) (insert alpha alpha)
      (insert (ZFSet.pair alpha (refinementFormulaDataCode d)) history) levels =
      M.stageTwoConditions rows I levels alpha d := by
  apply ZFSet.ext
  intro z
  rw [M.mem_forcingHistoryConditions, M.mem_stageTwoConditions,
    forcingHistoryConditionCode_insert_iff function (ZFSet.mem_irrefl alpha),
    packedSuccessorConditionCode_code_iff]
  constructor
  · rintro ⟨candidate, _, current⟩
    exact ⟨candidate, current⟩
  · rintro ⟨candidate, current⟩
    obtain ⟨row, A, equal, member, tests⟩ := current
    rw [lower] at member
    have priorCut := ((M.mem_forcingHistoryConditions rows oldI (d 6) alpha history levels _).1 member).2
    have prior := (forcingHistoryConditionCode_ordinalCut_iff M alpha history levels alpha row A
      ordinal (fun _ hx => hx) coverage).1 priorCut
    exact ⟨candidate, equal.symm ▸ prior, row, A, equal, lower.symm ▸ member, tests⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundStructuralHistoryTestUnions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet



namespace PartitionPilot.Forcing
universe u




namespace RefinementDataHistory
variable {stages history T : ZFSet.{u}} (valid : RefinementDataHistory stages history T)
include valid

theorem append {alpha : ZFSet.{u}} (outside : alpha ∉ stages) (d : Fin 15 → ZFSet.{u})
    (terms : d 6 = T) (literal : RefinementIndexLevelCode (d 0) alpha) :
    RefinementDataHistory (insert alpha stages)
      (insert (ZFSet.pair alpha (refinementFormulaDataCode d)) history) T := by
  refine ⟨valid.function.insert outside _, ?_, ?_, ?_⟩
  · intro beta data entry
    rcases ZFSet.mem_insert_iff.1 entry with equal | old
    · exact ⟨d, (ZFSet.pair_inj.1 equal).2⟩
    · exact valid.decoded beta data old
  · intro beta fields entry
    rcases ZFSet.mem_insert_iff.1 entry with equal | old
    · have same := refinementFormulaDataCode_injective (ZFSet.pair_inj.1 equal).2
      exact (congrFun same 6).trans terms
    · exact valid.terms beta fields old
  · intro beta fields entry
    rcases ZFSet.mem_insert_iff.1 entry with equal | old
    · obtain ⟨rfl, code⟩ := ZFSet.pair_inj.1 equal
      have same := refinementFormulaDataCode_injective code
      exact (congrFun same 0).symm ▸ literal
    · exact valid.literal beta fields old

end RefinementDataHistory
end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRefinementCollisionSymmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u}
variable [PartialOrder P] [OrderTop P] (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)

theorem stageOneCollisionTest_symm (Rf Rc u u' w w' : (M.nameDomain s).names) (p : P)
    (collision : M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid
      Rf Rc u u' w w' p) :
    M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid
      Rf Rc u' u w' w p := by
  constructor
  · intro q hq facts
    exact collision.1 q hq ⟨Name.forcesEq_symm facts.1,
      fun r hr equal => facts.2 r hr (Name.forcesEq_symm equal)⟩
  · intro q hq facts
    exact collision.2 q hq ⟨Name.forcesEq_symm facts.1,
      fun r hr equal => facts.2 r hr (Name.forcesEq_symm equal)⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundAbsentLiftRangeCollisions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u}
variable [PartialOrder P] [OrderTop P] (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
variable (small : M.sets.Countable)

include small in
theorem stageOneCollisionTest_self (Rf Rc u w : (M.nameDomain s).names) (p : P) :
    M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid
      Rf Rc u u w w p := by
  unfold stageOneCollisionTest
  apply (M.ordinaryForces_iff_all_generics s small carrier _ _ p).2
  intro H hp generic
  let evaluated : TransitiveGround.{u} :=
    ⟨(M.nameDomain s).values {q | H.mem q}, (M.nameDomain s).values_transitive _⟩
  apply (evaluated.realize_refinementCollisionFormula _ (fun j => ⟨_, rfl⟩)).2
  exact ⟨fun _ => rfl, fun _ => rfl⟩

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable {T T2 : ZFSet.{u}} (hT : T ∈ M.sets)
variable (valid : ∀ z ∈ T, IsName s z) {valid2 : ∀ z ∈ T2, IsName s z}
variable (a : PosetAction G P) (b : Presentation L) (d : PosetAction G L)
variable (level : ZFSet.{u})
variable (indices : NiceRefinementIndexSystem M a s b d level T T2 valid valid2)

include indices in
theorem refinementVisibleLift_collisions (small : M.sets.Countable)
    (C E : L) (U Rf Rc u v w oldW visibility : (M.nameDomain s).names)
    (member : refinementIndexCode level (b.encode C) (b.encode E)
      U.val.val Rf.val.val Rc.val.val ∈ M.niceRefinementIndices a s b d level T T2 valid)
    (p : P) :
    let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
    let map := M.stageOneMapName s pairing unions powers separation collection carrier order hT valid U Rf Rc
    Name.ForcesMem p (cls Rf w).val visibility.val →
    Forces (M.nameDomain s) (BoundedFormula.pairMembershipFormula 0 1 2).toFormula
      ![cls Rf w, cls Rc u, map] p →
    Forces (M.nameDomain s) refinementCompatibilityFormula
      ![cls Rf oldW, visibility, cls Rc v, map] p →
    (∀ q, q ≤ p → ¬ Name.ForcesEq q (cls Rc u).val (cls Rc v).val) →
    (∀ q, q ≤ p → ¬ Name.ForcesEq q (cls Rf w).val (cls Rf oldW).val) ∧
    M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid
      Rf Rc u v w oldW p ∧
    M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid
      Rf Rc v u oldW w p ∧
    M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid
      Rf Rc u u w w p := by
  dsimp only
  let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
  let map := M.stageOneMapName s pairing unions powers separation collection carrier order hT valid U Rf Rc
  intro visible selected oldGuard different
  have coarseNegative : Forces (M.nameDomain s) (.neg (.equal 0 1)) ![cls Rc u, cls Rc v] p := different
  have values (H : ConditionFilter P) (hp : H.mem p)
      (generic : H.GenericFor (formulaFamily (M.nameDomain s))) :
      Name.eval {q | H.mem q} (cls Rc u).val ≠ Name.eval {q | H.mem q} (cls Rc v).val ∧
      Name.eval {q | H.mem q} (cls Rf w).val ≠ Name.eval {q | H.mem q} (cls Rf oldW).val := by
    have coarseDifferent : Name.eval {q | H.mem q} (cls Rc u).val ≠
        Name.eval {q | H.mem q} (cls Rc v).val :=
      forces_sound (M.nameDomain s) H generic (.neg (.equal 0 1)) ![cls Rc u, cls Rc v] hp coarseNegative
    refine ⟨coarseDifferent, ?_⟩
    intro sameFine
    have visibleValue := Name.forcesMem_sound (M.nameDomain s) H
      (fun D hD dense => generic D (Or.inl hD) dense)
      (cls Rf w).property visibility.property hp visible
    have oldVisible : Name.eval {q | H.mem q} (cls Rf oldW).val ∈
        Name.eval {q | H.mem q} visibility.val := sameFine ▸ visibleValue
    have oldEntry := M.refinementCompatibility_eval s
      ![cls Rf oldW, visibility, cls Rc v, map] H generic hp oldGuard oldVisible
    let evaluated : TransitiveGround.{u} :=
      ⟨(M.nameDomain s).values {q | H.mem q}, (M.nameDomain s).values_transitive _⟩
    have selectedTruth := forces_sound (M.nameDomain s) H generic
      (BoundedFormula.pairMembershipFormula 0 1 2).toFormula ![cls Rf w, cls Rc u, map] hp selected
    have selectedEntry : ZFSet.pair (Name.eval {q | H.mem q} (cls Rf w).val)
        (Name.eval {q | H.mem q} (cls Rc u).val) ∈ Name.eval {q | H.mem q} map.val :=
      (BoundedFormula.truth_pairMembershipFormula 0 1 2 _).1
        ((BoundedFormula.realize_toFormula evaluated _ _ (fun j => ⟨_, rfl⟩)).1 selectedTruth)
    obtain ⟨_, _, _, _, forced⟩ := (indices.typed_entries C E U Rf Rc).1 member
    have objects := M.refinementObjects_eval s pairing carrier hT valid indices.family_ground
      U Rf Rc H generic H.top_mem forced
    have oldEntry' : ZFSet.pair (Name.eval {q | H.mem q} (cls Rf w).val)
        (Name.eval {q | H.mem q} (cls Rc v).val) ∈ Name.eval {q | H.mem q} map.val :=
      sameFine.symm ▸ oldEntry
    exact coarseDifferent ((functionCode_partial objects.function).unique _ _ _ selectedEntry oldEntry')
  have fineNegative : Forces (M.nameDomain s) (.neg (.equal 0 1)) ![cls Rf w, cls Rf oldW] p := by
    apply (M.ordinaryForces_iff_all_generics s small carrier _ _ p).2
    intro H hp generic
    exact (values H hp generic).2
  have collision : M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid
      Rf Rc u v w oldW p := by
    apply (M.ordinaryForces_iff_all_generics s small carrier _ _ p).2
    intro H hp generic
    let evaluated : TransitiveGround.{u} :=
      ⟨(M.nameDomain s).values {q | H.mem q}, (M.nameDomain s).values_transitive _⟩
    apply (evaluated.realize_refinementCollisionFormula _ (fun j => ⟨_, rfl⟩)).2
    have differentValues := values H hp generic
    exact ⟨fun eq => False.elim (differentValues.1 eq), fun eq => False.elim (differentValues.2 eq)⟩
  exact ⟨fineNegative, collision,
    M.stageOneCollisionTest_symm s pairing unions powers separation collection carrier order hT valid
      Rf Rc u v w oldW p collision,
    M.stageOneCollisionTest_self s pairing unions powers separation collection carrier order hT valid
      small Rf Rc u w p⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundRefinementVisibleLiftInsertions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable {T T2 : ZFSet.{u}} (hT : T ∈ M.sets)
variable (valid : ∀ z ∈ T, IsName s z) {valid2 : ∀ z ∈ T2, IsName s z}
variable (a : PosetAction G P) (t : Presentation G)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (terms : ∀ g (z : Name s), z.val ∈ T → (a.act s g z).val ∈ T)
variable (system : NiceNameSystem M a s b d base directed T valid)
variable (level : ZFSet.{u})
variable (indices : NiceRefinementIndexSystem M a s b d level T T2 valid valid2)

include carrier in
private theorem visibility_forces_upward (small : M.sets.Countable)
    (z : (M.nameDomain s).names) (C v : L) (lower : C ≤ v) (p : P)
    (visible : Name.ForcesMem p z.val
      (M.stageOneVisibilityName s valid a b d base directed system C).val) :
    Name.ForcesMem p z.val
      (M.stageOneVisibilityName s valid a b d base directed system v).val := by
  let vis := M.stageOneVisibilityName s valid a b d base directed system
  change Forces (M.nameDomain s) (.mem 0 1) ![z, vis v] p
  apply (M.ordinaryForces_iff_all_generics s small carrier _ _ p).2
  intro H hp generic
  have seen := Name.forcesMem_sound (M.nameDomain s) H
    (fun D hD dense => generic D (Or.inl hD) dense) z.property (vis C).property hp visible
  exact (M.encode_mem_visibleSupportProfile a s b d T H _ v).1
    (M.visibleSupportProfile_upward a s b d T H _ lower
      ((M.encode_mem_visibleSupportProfile a s b d T H _ C).2 seen))

include maps terms indices in
theorem refinementVisibleLift_forces_coarse_visibility (small : M.sets.Countable)
    (C E : L) (U Rf Rc fine coarse : (M.nameDomain s).names)
    (member : refinementIndexCode level (b.encode C) (b.encode E)
      U.val.val Rf.val.val Rc.val.val ∈ M.niceRefinementIndices a s b d level T T2 valid)
    (p : P) :
    let vis := M.stageOneVisibilityName s valid a b d base directed system
    let map := M.stageOneMapName s pairing unions powers separation collection carrier order hT valid U Rf Rc
    Name.ForcesMem p fine.val (vis C).val →
    Forces (M.nameDomain s) (BoundedFormula.pairMembershipFormula 0 1 2).toFormula
      ![fine, coarse, map] p →
    Name.ForcesMem p coarse.val (vis C).val := by
  dsimp only
  let vis := M.stageOneVisibilityName s valid a b d base directed system
  let map := M.stageOneMapName s pairing unions powers separation collection carrier order hT valid U Rf Rc
  intro visible selected
  change Forces (M.nameDomain s) (.mem 0 1) ![coarse, vis C] p
  apply (M.ordinaryForces_iff_all_generics s small carrier _ _ p).2
  intro H hp generic
  have seen := Name.forcesMem_sound (M.nameDomain s) H
    (fun D hD dense => generic D (Or.inl hD) dense) fine.property (vis C).property hp visible
  let evaluated : TransitiveGround.{u} :=
    ⟨(M.nameDomain s).values {q | H.mem q}, (M.nameDomain s).values_transitive _⟩
  have selectedTruth := forces_sound (M.nameDomain s) H generic
    (BoundedFormula.pairMembershipFormula 0 1 2).toFormula ![fine, coarse, map] hp selected
  have entry : ZFSet.pair (Name.eval {q | H.mem q} fine.val)
      (Name.eval {q | H.mem q} coarse.val) ∈ Name.eval {q | H.mem q} map.val :=
    (BoundedFormula.truth_pairMembershipFormula 0 1 2 _).1
      ((BoundedFormula.realize_toFormula evaluated _ _ (fun j => ⟨_, rfl⟩)).1 selectedTruth)
  exact M.niceRefinementIndex_preserves_visibility s pairing unions powers separation collection
    carrier order a t maps b d base directed hT terms system indices C E U Rf Rc member
    le_rfl H generic seen entry

include maps terms indices in
theorem stageOneSingleTests_visible_lift (small : M.sets.Countable)
    (C E : L) (U Rf Rc u w : (M.nameDomain s).names)
    (member : refinementIndexCode level (b.encode C) (b.encode E)
      U.val.val Rf.val.val Rc.val.val ∈ M.niceRefinementIndices a s b d level T T2 valid)
    (p : P) (activeU : Name.ForcesMem p u.val U.val)
    (activeW : Name.ForcesMem p w.val U.val) :
    let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
    let vis := M.stageOneVisibilityName s valid a b d base directed system
    let map := M.stageOneMapName s pairing unions powers separation collection carrier order hT valid U Rf Rc
    Name.ForcesMem p (cls Rf w).val (vis C).val →
    Forces (M.nameDomain s) (BoundedFormula.pairMembershipFormula 0 1 2).toFormula
      ![cls Rf w, cls Rc u, map] p →
    M.stageOneSingleTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system C E U Rf Rc u w p := by
  dsimp only
  let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
  let vis := M.stageOneVisibilityName s valid a b d base directed system
  let map := M.stageOneMapName s pairing unions powers separation collection carrier order hT valid U Rf Rc
  intro visible selected
  have coarseVisible := M.refinementVisibleLift_forces_coarse_visibility s pairing unions powers
    separation collection carrier order hT valid a t maps b d base directed terms system level indices
    small C E U Rf Rc (cls Rf w) (cls Rc u) member p visible selected
  have above := ((indices.typed_entries C E U Rf Rc).1 member).1.le
  refine ⟨⟨activeU, activeW⟩, ?_, ?_⟩
  · intro v hv
    have fineAbove := visibility_forces_upward M s carrier valid a b d base directed system
      small (cls Rf w) C v (above.trans hv) p visible
    have coarseAbove := visibility_forces_upward M s carrier valid a b d base directed system
      small (cls Rc u) C v (above.trans hv) p coarseVisible
    apply (M.ordinaryForces_iff_all_generics s small carrier _ _ p).2
    intro H hp generic
    let evaluated : TransitiveGround.{u} :=
      ⟨(M.nameDomain s).values {q | H.mem q}, (M.nameDomain s).values_transitive _⟩
    apply (evaluated.realize_refinementProfileFormula _ (fun j => ⟨_, rfl⟩)).2
    have fineSeen := Name.forcesMem_sound (M.nameDomain s) H
      (fun D hD dense => generic D (Or.inl hD) dense) (cls Rf w).property (vis v).property hp fineAbove
    have coarseSeen := Name.forcesMem_sound (M.nameDomain s) H
      (fun D hD dense => generic D (Or.inl hD) dense) (cls Rc u).property (vis v).property hp coarseAbove
    exact ⟨fun _ => fineSeen, fun _ => coarseSeen⟩
  · apply (M.ordinaryForces_iff_all_generics s small carrier _ _ p).2
    intro H hp generic
    let evaluated : TransitiveGround.{u} :=
      ⟨(M.nameDomain s).values {q | H.mem q}, (M.nameDomain s).values_transitive _⟩
    apply (evaluated.realize_refinementCompatibilityFormula _ (fun j => ⟨_, rfl⟩)).2
    intro _
    have selectedTruth := forces_sound (M.nameDomain s) H generic
      (BoundedFormula.pairMembershipFormula 0 1 2).toFormula ![cls Rf w, cls Rc u, map] hp selected
    exact (BoundedFormula.truth_pairMembershipFormula 0 1 2 _).1
      ((BoundedFormula.realize_toFormula evaluated _ _ (fun j => ⟨_, rfl⟩)).1 selectedTruth)

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
universe u

variable (M : TransitiveGround.{u}) (d : Fin 15 → ZFSet.{u})

theorem stageOneRawTests_insert {A lower t u w : ZFSet.{u}}
    (tests : stageOneRawTests M d A lower)
    (single : stageOneRawSingle M d t u w lower)
    (old_new : ∀ v ∈ d 6, ∀ z ∈ d 6, stageOneAssignment t v z ∈ A →
      stageOneRawCollision M d t v u z w lower)
    (new_old : ∀ v ∈ d 6, ∀ z ∈ d 6, stageOneAssignment t v z ∈ A →
      stageOneRawCollision M d t u v w z lower)
    (self : stageOneRawCollision M d t u u w w lower) :
    stageOneRawTests M d (insert (stageOneAssignment t u w) A) lower := by
  refine ⟨?_, ?_⟩
  · intro i hi v hv z hz entry
    rcases ZFSet.mem_insert_iff.1 entry with equal | old
    · obtain ⟨rfl, rfl, rfl⟩ := (stageOneAssignment_eq_iff i v z t u w).1 equal
      exact single
    · exact tests.1 i hi v hv z hz old
  · intro i hi v hv v' hv' z hz z' hz' entry entry'
    rcases ZFSet.mem_insert_iff.1 entry with equal | old
    · obtain ⟨rfl, rfl, rfl⟩ := (stageOneAssignment_eq_iff i v z t u w).1 equal
      rcases ZFSet.mem_insert_iff.1 entry' with equal' | old'
      · obtain ⟨_, rfl, rfl⟩ := (stageOneAssignment_eq_iff _ _ _ _ _ _).1 equal'
        exact self
      · exact new_old v' hv' z' hz' old'
    · rcases ZFSet.mem_insert_iff.1 entry' with equal' | old'
      · obtain ⟨rfl, rfl, rfl⟩ := (stageOneAssignment_eq_iff i v' z' t u w).1 equal'
        exact old_new v hv z hz old
      · exact tests.2 i hi v hv v' hv' z hz z' hz' old old'

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

theorem assignmentCut_insert_current {J stages levels alpha z A : ZFSet.{u}}
    (function : ZFSet.IsFunc J stages levels)
    (level : ZFSet.pair z alpha ∈ levels) :
    assignmentCut levels alpha (insert z A) = assignmentCut levels alpha A := by
  apply ZFSet.ext
  intro x
  rw [mem_assignmentCut, mem_assignmentCut]
  constructor
  · rintro ⟨member, xi, hxi, entry⟩
    rcases ZFSet.mem_insert_iff.1 member with rfl | old
    · have hz := (ZFSet.pair_mem_prod.1 (function.1 level)).1
      obtain ⟨value, _, unique⟩ := function.2 _ hz
      have equal : xi = alpha := (unique xi entry).trans (unique alpha level).symm
      exact False.elim (ZFSet.mem_irrefl alpha (equal ▸ hxi))
    · exact ⟨old, xi, hxi, entry⟩
  · rintro ⟨member, below⟩
    exact ⟨ZFSet.mem_insert_of_mem _ member, below⟩

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})

theorem stageTwoConditions_insert
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {rows I levels stages alpha row A t u w : ZFSet.{u}} (d : Fin 15 → ZFSet.{u})
    (function : ZFSet.IsFunc (stageOneAssignments I (d 6)) stages levels)
    (level : ZFSet.pair (stageOneAssignment t u w) alpha ∈ levels)
    (ground : stageOneAssignment t u w ∈ M.sets)
    (member : ZFSet.pair row A ∈ M.stageTwoConditions rows I levels alpha d)
    (single : stageOneRawSingle M d t u w (ZFSet.pair row (assignmentCut levels alpha A)))
    (old_new : ∀ v ∈ d 6, ∀ z ∈ d 6, stageOneAssignment t v z ∈ A →
      stageOneRawCollision M d t v u z w (ZFSet.pair row (assignmentCut levels alpha A)))
    (new_old : ∀ v ∈ d 6, ∀ z ∈ d 6, stageOneAssignment t v z ∈ A →
      stageOneRawCollision M d t u v w z (ZFSet.pair row (assignmentCut levels alpha A)))
    (self : stageOneRawCollision M d t u u w w (ZFSet.pair row (assignmentCut levels alpha A))) :
    ZFSet.pair row (insert (stageOneAssignment t u w) A) ∈
      M.stageTwoConditions rows I levels alpha d ∧
    assignmentCut levels alpha (insert (stageOneAssignment t u w) A) =
      assignmentCut levels alpha A := by
  have cut := assignmentCut_insert_current function level (A := A)
  obtain ⟨hrow, hA, subset, small, lower, tests⟩ :=
    (M.pair_mem_stageTwoConditions rows I levels alpha d row A).1 member
  refine ⟨(M.pair_mem_stageTwoConditions rows I levels alpha d row _).2 ?_, cut⟩
  refine ⟨hrow, M.insert_mem pairing unions ground hA, ?_,
    M.groundEmbeddable_insert pairing unions powers separation infinite hA ground small, ?_, ?_⟩
  · intro x hx
    rcases ZFSet.mem_insert_iff.1 hx with rfl | old
    · exact (ZFSet.pair_mem_prod.1 (function.1 level)).1
    · exact subset old
  · simpa only [cut] using lower
  · simpa only [cut] using stageOneRawTests_insert M d tests single old_new new_old self

end TransitiveGround

end PartitionPilot.Forcing




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (level : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets)
variable {T T2 : ZFSet.{u}} (hT : T ∈ M.sets)
variable (valid : ∀ z ∈ T, IsName s z) {valid2 : ∀ z ∈ T2, IsName s z}
variable (indices : NiceRefinementIndexSystem M a s b d level T T2 valid valid2)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable (terms : ∀ g (sigma : Name s), sigma.val ∈ T → (a.act s g sigma).val ∈ T)
variable (small : M.sets.Countable)
include maps terms indices nodes small

theorem refinementLevelRawTests_insert_visibleLift
    (C E : L) (U Rf Rc u w : (M.nameDomain s).names)
    (member : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d level T T2 valid)
    {A : ZFSet.{u}} (p : P)
    (tests : stageOneRawTests M (M.refinementLevelFormulaData a s b d level T T2 valid) A (s.encode p))
    (activeU : Name.ForcesMem p u.val U.val) (activeW : Name.ForcesMem p w.val U.val) :
    let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
    let vis := M.stageOneVisibilityName s valid a b d base directed system
    let map := M.stageOneMapName s pairing unions powers separation collection carrier order hT valid U Rf Rc
    Name.ForcesMem p (cls Rf w).val (vis C).val →
    Forces (M.nameDomain s) (BoundedFormula.pairMembershipFormula 0 1 2).toFormula
      ![cls Rf w, cls Rc u, map] p →
    (∀ (v z : (M.nameDomain s).names), v.val.val ∈ T → z.val.val ∈ T →
      stageOneAssignment (refinementIndexCode level (b.encode C) (b.encode E)
        U.val.val Rf.val.val Rc.val.val) v.val.val z.val.val ∈ A →
      ∀ q, q ≤ p → ¬ Name.ForcesEq q (cls Rc u).val (cls Rc v).val) →
    stageOneRawTests M (M.refinementLevelFormulaData a s b d level T T2 valid)
      (insert (stageOneAssignment (refinementIndexCode level (b.encode C) (b.encode E)
        U.val.val Rf.val.val Rc.val.val) u.val.val w.val.val) A) (s.encode p) := by
  dsimp only
  let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
  let vis := M.stageOneVisibilityName s valid a b d base directed system
  intro visible mapped fresh
  have single := M.refinementLevelRawSingle_iff a s b d level pairing unions powers separation collection
    carrier order nodes hT valid indices base directed system
  have collision := M.refinementLevelRawCollision_iff a s b d level pairing unions powers separation collection
    carrier order hT valid indices
  have mixed (v z : (M.nameDomain s).names) (hv : v.val.val ∈ T) (hz : z.val.val ∈ T)
      (old : stageOneAssignment (refinementIndexCode level (b.encode C) (b.encode E)
        U.val.val Rf.val.val Rc.val.val) v.val.val z.val.val ∈ A) :=
    M.refinementVisibleLift_collisions s pairing unions powers separation collection carrier order hT valid
      a b d level indices small C E U Rf Rc u v w z (vis C) member p visible mapped
      ((single C E U Rf Rc v z member p).1 (tests.1 _ member _ hv _ hz old)).2.2
      (fresh v z hv hz old)
  apply stageOneRawTests_insert M (M.refinementLevelFormulaData a s b d level T T2 valid) tests
  · exact (single C E U Rf Rc u w member p).2
      (M.stageOneSingleTests_visible_lift s pairing unions powers separation collection carrier order hT valid
        a t maps b d base directed terms system level indices small C E U Rf Rc u w member p
        activeU activeW visible mapped)
  · intro v hv z hz old
    let vn : (M.nameDomain s).names := ⟨⟨v, valid v hv⟩, M.transitive hT hv⟩
    let zn : (M.nameDomain s).names := ⟨⟨z, valid z hz⟩, M.transitive hT hz⟩
    exact (collision C E U Rf Rc vn u zn w member p).2 (mixed vn zn hv hz old).2.2.1
  · intro v hv z hz old
    let vn : (M.nameDomain s).names := ⟨⟨v, valid v hv⟩, M.transitive hT hv⟩
    let zn : (M.nameDomain s).names := ⟨⟨z, valid z hz⟩, M.transitive hT hz⟩
    exact (collision C E U Rf Rc u vn w zn member p).2 (mixed vn zn hv hz old).2.1
  · exact (collision C E U Rf Rc u u w w member p).2
      (M.stageOneCollisionTest_self s pairing unions powers separation collection carrier order hT valid
        small Rf Rc u w p)

end PartitionPilot.Forcing.TransitiveGround

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



namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem forcingHistoryConditions_levels_congr (rows I T stages history first second : ZFSet.{u})
    (cuts : ∀ beta ∈ stages, ∀ A, assignmentCut first beta A = assignmentCut second beta A) :
    M.forcingHistoryConditions rows I T stages history first =
      M.forcingHistoryConditions rows I T stages history second := by
  apply ZFSet.ext
  intro z
  rw [M.mem_forcingHistoryConditions, M.mem_forcingHistoryConditions]
  exact and_congr Iff.rfl (forcingHistoryConditionCode_levels_congr M stages history first second z cuts)

end TransitiveGround
namespace RecursiveRefinementDataHistory
variable {M : TransitiveGround.{u}} {rows T alpha history : ZFSet.{u}}
variable (run : RecursiveRefinementDataHistory M rows T alpha history)
include run

theorem append (ordinal : ordinalSetProperty alpha) (d : Fin 15 → ZFSet.{u})
    (terms : d 6 = T) (literal : RefinementIndexLevelCode (d 0) alpha)
    (lower : d 7 = M.refinementHistoryForcing rows T alpha history) :
    RecursiveRefinementDataHistory M rows T (insert alpha alpha)
      (insert (ZFSet.pair alpha (refinementFormulaDataCode d)) history) := by
  refine ⟨run.data.append (ZFSet.mem_irrefl alpha) d terms literal, ?_⟩
  intro beta fields entry
  rcases ZFSet.mem_insert_iff.1 entry with equal | old
  · obtain ⟨rfl, code⟩ := ZFSet.pair_inj.1 equal
    have same := refinementFormulaDataCode_injective code
    rw [graphRestriction_insert_of_not_mem (ZFSet.mem_irrefl beta), run.data.function.restriction_eq]
    exact (congrFun same 7).trans lower
  · have hbeta := run.data.function.pair_source old
    have outside : alpha ∉ beta := fun member =>
      ZFSet.mem_irrefl alpha (ordinal.1 beta hbeta alpha member)
    rw [graphRestriction_insert_of_not_mem outside]
    exact run.carrier beta fields old

theorem successor_eq (ordinal : ordinalSetProperty alpha) (d : Fin 15 → ZFSet.{u})
    (terms : d 6 = T) (literal : RefinementIndexLevelCode (d 0) alpha)
    (lower : d 7 = M.refinementHistoryForcing rows T alpha history) :
    let next := insert (ZFSet.pair alpha (refinementFormulaDataCode d)) history
    M.refinementHistoryForcing rows T (insert alpha alpha) next =
      M.stageTwoConditions rows (refinementDataHistoryIndices (insert alpha alpha) next)
        (refinementDataHistoryLevels (insert alpha alpha) next T) alpha d := by
  let next := insert (ZFSet.pair alpha (refinementFormulaDataCode d)) history
  let levels := refinementDataHistoryLevels (insert alpha alpha) next T
  let oldI := refinementDataHistoryIndices alpha history
  have extended := run.append ordinal d terms literal lower
  have subset : alpha ⊆ insert alpha alpha := fun _ member => ZFSet.mem_insert_of_mem alpha member
  have prefixHistory : graphRestriction alpha next = history := by
    rw [graphRestriction_insert_of_not_mem (ZFSet.mem_irrefl alpha), run.data.function.restriction_eq]
  have cuts : ∀ beta ∈ alpha, ∀ A,
      assignmentCut (refinementDataHistoryLevels alpha history T) beta A = assignmentCut levels beta A := by
    intro beta hbeta A
    have equal := extended.data.prefix_cut subset (ordinal.1 beta hbeta) A
    rw [prefixHistory] at equal
    exact equal
  have lowerGlobal : d 7 = M.forcingHistoryConditions rows oldI (d 6) alpha history levels := by
    calc
      d 7 = M.refinementHistoryForcing rows T alpha history := lower
      _ = M.forcingHistoryConditions rows oldI T alpha history levels :=
        M.forcingHistoryConditions_levels_congr rows oldI T alpha history _ levels cuts
      _ = M.forcingHistoryConditions rows oldI (d 6) alpha history levels := by rw [terms]
  have coverage : ForcingHistoryLevelCoverage alpha history levels := by
    intro beta hbeta fields entry t ht u hu w hw
    exact extended.data.coverage beta (ZFSet.mem_insert_of_mem alpha hbeta) fields
      (ZFSet.mem_insert_of_mem _ entry) t ht u hu w hw
  simpa only [terms, TransitiveGround.refinementHistoryForcing, levels, next] using
    (M.forcingHistoryConditions_successor_eq rows oldI (refinementDataHistoryIndices (insert alpha alpha) next)
      alpha history levels d run.data.function ordinal coverage lowerGlobal)

end RecursiveRefinementDataHistory
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.RecursiveRefinementDataHistory
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {rows T alpha history : ZFSet.{u}}
variable (run : RecursiveRefinementDataHistory M rows T alpha history)
include run

theorem successor_insert_extension
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (ordinal : ordinalSetProperty alpha) (d : Fin 15 → ZFSet.{u})
    (terms : d 6 = T) (literal : RefinementIndexLevelCode (d 0) alpha)
    (lower : d 7 = M.refinementHistoryForcing rows T alpha history)
    (hI : d 0 ∈ M.sets) (hT : T ∈ M.sets)
    (rowOrder : ZFSet.{u}) (rowOrderLaw : PartialOrderCode rows rowOrder)
    {row A t u w : ZFSet.{u}} (index : t ∈ d 0) (first : u ∈ T) (second : w ∈ T) :
    let next := insert (ZFSet.pair alpha (refinementFormulaDataCode d)) history
    let levels := refinementDataHistoryLevels (insert alpha alpha) next T
    let P := M.refinementHistoryForcing rows T (insert alpha alpha) next
    ZFSet.pair row A ∈ P →
    stageOneRawSingle M d t u w (ZFSet.pair row (assignmentCut levels alpha A)) →
    (∀ v ∈ T, ∀ z ∈ T, stageOneAssignment t v z ∈ A →
      stageOneRawCollision M d t v u z w (ZFSet.pair row (assignmentCut levels alpha A))) →
    (∀ v ∈ T, ∀ z ∈ T, stageOneAssignment t v z ∈ A →
      stageOneRawCollision M d t u v w z (ZFSet.pair row (assignmentCut levels alpha A))) →
    stageOneRawCollision M d t u u w w (ZFSet.pair row (assignmentCut levels alpha A)) →
    ZFSet.pair row (insert (stageOneAssignment t u w) A) ∈ P ∧
      assignmentCut levels alpha (insert (stageOneAssignment t u w) A) =
        assignmentCut levels alpha A ∧
      ZFSet.pair (ZFSet.pair row (insert (stageOneAssignment t u w) A)) (ZFSet.pair row A) ∈
        M.refinementHistoryOrder rows rowOrder T (insert alpha alpha) next := by
  dsimp only
  intro member single old_new new_old self
  let next := insert (ZFSet.pair alpha (refinementFormulaDataCode d)) history
  have extended := run.append ordinal d terms literal lower
  have stored : ZFSet.pair alpha (refinementFormulaDataCode d) ∈ next := ZFSet.mem_insert _ _
  have level := extended.data.coverage alpha (ZFSet.mem_insert alpha alpha) d stored
    t index u (terms.symm ▸ first) w (terms.symm ▸ second)
  have function : ZFSet.IsFunc
      (stageOneAssignments (refinementDataHistoryIndices (insert alpha alpha) next) (d 6))
      (insert alpha alpha) (refinementDataHistoryLevels (insert alpha alpha) next T) := by
    simpa only [terms] using extended.data.levels_function
  have ground := M.stageOneAssignment_mem pairing (M.transitive hI index)
    (M.transitive hT first) (M.transitive hT second)
  have successor := run.successor_eq ordinal d terms literal lower
  have flat := successor ▸ member
  have result := M.stageTwoConditions_insert pairing unions powers separation infinite d
    function level ground flat single
    (fun v hv z hz old => old_new v (terms ▸ hv) z (terms ▸ hz) old)
    (fun v hv z hz old => new_old v (terms ▸ hv) z (terms ▸ hz) old) self
  have inserted := successor.symm ▸ result.1
  have candidate := ((M.mem_refinementHistoryForcing rows T (insert alpha alpha) next _).1 member).1
  have rowMember := ((M.pair_mem_stageOneCandidateBound _ _ _ _ _).1 candidate).1
  refine ⟨inserted, result.2, ?_⟩
  exact (M.pair_mem_refinementHistoryOrder rows rowOrder T (insert alpha alpha) next _ _ _ _).2
    ⟨inserted, member, rowOrderLaw.refl row rowMember, fun _ h => ZFSet.mem_insert_of_mem _ h⟩

end PartitionPilot.Forcing.RecursiveRefinementDataHistory



namespace PartitionPilot.Forcing
universe u





namespace FunctionGraphOn

theorem restriction_successor_entry {stages history alpha value : ZFSet.{u}}
    (function : FunctionGraphOn stages history)
    (entry : ZFSet.pair alpha value ∈ history) :
    graphRestriction (Insert.insert alpha alpha) history =
      Insert.insert (ZFSet.pair alpha value) (graphRestriction alpha history) := by
  apply ZFSet.ext
  intro z
  constructor
  · intro member
    obtain ⟨beta, hbeta, code, rfl, stored⟩ := mem_graphRestriction.1 member
    rcases ZFSet.mem_insert_iff.1 hbeta with equal | before
    · subst beta
      have same := function.unique stored entry
      exact ZFSet.mem_insert_iff.2 (Or.inl (congrArg (ZFSet.pair alpha) same))
    · exact ZFSet.mem_insert_of_mem _ (pair_mem_graphRestriction.2 ⟨stored, before⟩)
  · intro member
    rcases ZFSet.mem_insert_iff.1 member with equal | before
    · rw [equal]
      exact pair_mem_graphRestriction.2 ⟨entry, ZFSet.mem_insert alpha alpha⟩
    · obtain ⟨beta, hbeta, code, rfl, stored⟩ := mem_graphRestriction.1 before
      exact pair_mem_graphRestriction.2 ⟨stored, ZFSet.mem_insert_of_mem alpha hbeta⟩

end FunctionGraphOn

namespace RecursiveRefinementDataHistory
open SetFormula
variable {M : TransitiveGround.{u}} {rows T stages history : ZFSet.{u}}
variable (run : RecursiveRefinementDataHistory M rows T stages history)
include run

theorem stored_successor_eq (ordinal : ordinalSetProperty stages)
    {alpha : ZFSet.{u}} (member : alpha ∈ stages) (fields : Fin 15 → ZFSet.{u})
    (stored : ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ history) :
    let next := graphRestriction (insert alpha alpha) history
    M.refinementHistoryForcing rows T (insert alpha alpha) next =
      M.stageTwoConditions rows (refinementDataHistoryIndices (insert alpha alpha) next)
        (refinementDataHistoryLevels (insert alpha alpha) next T) alpha fields := by
  dsimp only
  rw [run.data.function.restriction_successor_entry stored]
  exact (run.restrict (ordinalSetProperty_member ordinal member) (ordinal.1 alpha member)).successor_eq
    (ordinalSetProperty_member ordinal member) fields (run.data.terms alpha fields stored)
    (run.data.literal alpha fields stored) (run.carrier alpha fields stored)

theorem stored_successor_insert_extension
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (ordinal : ordinalSetProperty stages) {alpha : ZFSet.{u}} (member : alpha ∈ stages)
    (fields : Fin 15 → ZFSet.{u})
    (stored : ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ history)
    (hI : fields 0 ∈ M.sets) (hT : T ∈ M.sets)
    (rowOrder : ZFSet.{u}) (rowOrderLaw : PartialOrderCode rows rowOrder)
    {row A idx u w : ZFSet.{u}} (index : idx ∈ fields 0) (first : u ∈ T) (second : w ∈ T) :
    let next := graphRestriction (insert alpha alpha) history
    let levels := refinementDataHistoryLevels (insert alpha alpha) next T
    let P := M.refinementHistoryForcing rows T (insert alpha alpha) next
    ZFSet.pair row A ∈ P →
    stageOneRawSingle M fields idx u w (ZFSet.pair row (assignmentCut levels alpha A)) →
    (∀ v ∈ T, ∀ z ∈ T, stageOneAssignment idx v z ∈ A →
      stageOneRawCollision M fields idx v u z w (ZFSet.pair row (assignmentCut levels alpha A))) →
    (∀ v ∈ T, ∀ z ∈ T, stageOneAssignment idx v z ∈ A →
      stageOneRawCollision M fields idx u v w z (ZFSet.pair row (assignmentCut levels alpha A))) →
    stageOneRawCollision M fields idx u u w w (ZFSet.pair row (assignmentCut levels alpha A)) →
    ZFSet.pair row (insert (stageOneAssignment idx u w) A) ∈ P ∧
      assignmentCut levels alpha (insert (stageOneAssignment idx u w) A) =
        assignmentCut levels alpha A ∧
      ZFSet.pair (ZFSet.pair row (insert (stageOneAssignment idx u w) A)) (ZFSet.pair row A) ∈
        M.refinementHistoryOrder rows rowOrder T (insert alpha alpha) next := by
  dsimp only
  rw [run.data.function.restriction_successor_entry stored]
  exact (run.restrict (ordinalSetProperty_member ordinal member) (ordinal.1 alpha member)).successor_insert_extension
    pairing unions powers separation infinite (ordinalSetProperty_member ordinal member) fields
    (run.data.terms alpha fields stored) (run.data.literal alpha fields stored)
    (run.carrier alpha fields stored) hI hT rowOrder rowOrderLaw index first second

end RecursiveRefinementDataHistory
end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticRepresentedDomainAbsentLift
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

local notation "next" => graphRestriction (insert alpha alpha) packed
local notation "upper" => M.refinementHistoryForcing c.carrier T (insert alpha alpha) next
local notation "levels" => refinementDataHistoryLevels (insert alpha alpha) next T
local notation "packedGround" => M.structuralRefinementHistory_mem pairing unions powers separation collection
  ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
  (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
    (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
local notation "lowerGround" => M.refinementHistoryForcing_mem pairing unions powers separation
  carrier hT hAlpha (M.graphRestriction_mem unions separation hAlpha packedGround) omega
local notation "orderGround" => M.refinementHistoryOrder_mem pairing unions powers separation
  carrier rowOrderGround hT hAlpha (M.graphRestriction_mem unions separation hAlpha packedGround) omega

theorem semanticStructuralSuccessor_insert_visibleLift_oai
    (infinite : Realize M.sets infinity Fin.elim0) (small : M.sets.Countable)
    {row A : ZFSet.{u}} (condition : ZFSet.pair row A ∈ upper) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation Q
    let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    let system := M.semanticStructuralPrefix_refinementSystem c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace member
    let lowerOrder : lower.conditionOrder ∈ M.sets := by
      rw [M.refinementHistoryDecodedOrder_eq]
      exact orderGround
    let cls := M.stageOneClassName lower pairing unions powers separation collection lowerGround lowerOrder hT valid
    let vis := M.stageOneVisibilityName lower valid act b d base directed system.first
    ∀ (C E : L) (U Rf Rc u w : (M.nameDomain lower).names),
      let idx := refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
      idx ∈ M.niceRefinementIndices act lower b d alpha T T2 valid →
      u.val.val ∈ T → w.val.val ∈ T →
      ∀ pCut : SetMembers Q,
      lower.encode pCut = ZFSet.pair row (assignmentCut levels alpha A) →
      Name.ForcesMem pCut u.val U.val → Name.ForcesMem pCut w.val U.val →
      Name.ForcesMem pCut (cls Rf w).val (vis C).val →
      Forces (M.nameDomain lower) (BoundedFormula.pairMembershipFormula 0 1 2).toFormula
        ![cls Rf w, cls Rc u, M.stageOneMapName lower pairing unions powers separation collection
          lowerGround lowerOrder hT valid U Rf Rc] pCut →
      (∀ v z : (M.nameDomain lower).names, v.val.val ∈ T → z.val.val ∈ T →
        stageOneAssignment idx v.val.val z.val.val ∈ A →
        ∀ q, q ≤ pCut → ¬ Name.ForcesEq q (cls Rc u).val (cls Rc v).val) →
      ZFSet.pair row (insert (stageOneAssignment idx u.val.val w.val.val) A) ∈ upper ∧
        assignmentCut levels alpha (insert (stageOneAssignment idx u.val.val w.val.val) A) =
          assignmentCut levels alpha A ∧
        ZFSet.pair (ZFSet.pair row (insert (stageOneAssignment idx u.val.val w.val.val) A))
          (ZFSet.pair row A) ∈ M.refinementHistoryOrder c.carrier c.conditionOrder T (insert alpha alpha) next := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  let system := M.semanticStructuralPrefix_refinementSystem c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  have lowerOrder : lower.conditionOrder ∈ M.sets := by
    rw [M.refinementHistoryDecodedOrder_eq]
    exact orderGround
  dsimp only
  intro C E U Rf Rc u w idx hu hw pCut cutCode activeU activeW visible mapped fresh
  let fields := M.refinementLevelFormulaData act lower b d alpha T T2 valid
  let index := refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
  have stored := M.semanticStructuralPrefix_refinementData_entry c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  have same := (run).carriers.stored_successor_eq ordinal member fields stored
  have old := (M.pair_mem_stageTwoConditions c.carrier
    (refinementDataHistoryIndices (insert alpha alpha) next) levels alpha fields row A).1 (same ▸ condition)
  have oldTests : stageOneRawTests M fields A (lower.encode pCut) := by
    rw [cutCode]
    exact old.2.2.2.2.2
  have allTests := M.refinementLevelRawTests_insert_visibleLift act lower t b d alpha
    pairing unions powers separation collection lowerGround lowerOrder nodes hT valid system.indices
    base directed system.first system.inputs.condition_maps system.inputs.terms_closed small
    C E U Rf Rc u w idx pCut oldTests activeU activeW visible mapped fresh
  have inserted : stageOneAssignment index u.val.val w.val.val ∈
      insert (stageOneAssignment index u.val.val w.val.val) A := ZFSet.mem_insert _ _
  have indexMem : index ∈ fields 0 := idx
  rw [cutCode] at allTests
  exact (run).carriers.stored_successor_insert_extension pairing unions powers separation infinite
    ordinal member fields stored system.indices.index_ground hT c.conditionOrder c.conditionOrder_code
    indexMem hu hw condition (allTests.1 index indexMem _ hu _ hw inserted)
    (fun v hv z hz old => allTests.2 index indexMem v hv _ hu z hz _ hw
      (ZFSet.mem_insert_of_mem _ old) inserted)
    (fun v hv z hz old => allTests.2 index indexMem _ hu v hv _ hw z hz
      inserted (ZFSet.mem_insert_of_mem _ old))
    (allTests.2 index indexMem _ hu _ hu _ hw _ hw inserted inserted)

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

theorem solution.{u} : type_of% @OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralSuccessor_insert_visibleLift_oai.{u} := @OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralSuccessor_insert_visibleLift_oai.{u}
