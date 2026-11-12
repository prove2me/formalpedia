-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.exists_groundFairPreparationOrbit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:25:07.295193+00:00
-- url     : https://prove2.me/submissions/3f2022f5-5cf3-4a00-a4fe-4f4b724ea45f

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
import Theorems.Thm_OAI_PartitionPilot_Forcing_GroundMainPrefix_FinalSupportFulfillment_exists_prefixPreparationBatch

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

namespace FunctionGraphOn

theorem successor {A f : ZFSet.{u}} (h : FunctionGraphOn A f) (y : ZFSet.{u}) :
    FunctionGraphOn (Insert.insert A A) (Insert.insert (ZFSet.pair A y) f) :=
  h.insert (ZFSet.mem_irrefl A) y

end FunctionGraphOn

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_PresentedGroupCodes
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



end OAI
end

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

end PartitionPilot.Forcing.SetFormula

end

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

namespace TransitiveGround

open SetRealization SetFormula Compression.RecursiveMaps
universe u v
variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P)

theorem codedFamily_countable (small : M.sets.Countable) : (M.codedFamily s).Countable :=
  small.image _

end TransitiveGround



namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem exists_coded_ordinary_generic (small : M.sets.Countable)
    (carrier : s.carrier ∈ M.sets) (p : P) :
    ∃ H : ConditionFilter P, H.mem p ∧ H.GenericFor (M.codedFamily s) ∧
      H.GenericFor (formulaFamily (M.nameDomain s)) := by
  let conditionsCountable : Countable P := M.conditions_countable s small carrier
  have ordinary := formulaFamily_countable (M.nameDomain s) (M.nameDomain_countable s small)
  obtain ⟨H, member, generic⟩ := exists_generic_for_countable_family p
    (M.codedFamily s ∪ formulaFamily (M.nameDomain s))
    ((M.codedFamily_countable s small).union ordinary)
  exact ⟨H, member, (fun E hE => generic E (Or.inl hE)),
    fun E hE => generic E (Or.inr hE)⟩

end TransitiveGround



end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_FinitePrincipalNameSupports
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetRealization Compression.RecursiveMaps Compression.RecursiveMaps.CosetGeometry.OrderAction
universe u v
variable {P : Type u} [PartialOrder P] {G : Type v} [Group G]

variable (a : PosetAction G P) (s : Presentation P)

theorem niceNameCode_subset {T z : ZFSet.{u}} {K : Subgroup G}
    (code : NiceNameCode a s T K z) : z ⊆ ZFSet.prod T s.carrier := by
  obtain ⟨τ, equal, subset, _⟩ := code
  exact equal ▸ subset

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

namespace BoundedFormula

open SetFormula

theorem truth_coinitialBelowFormula {n} (order F target B : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (coinitialBelowFormula order F target B) env ↔
      CoinitialBelowCode (env order) (env F) (env target) (env B) := by
  simp only [coinitialBelowFormula, Truth, truth_exMem, truth_pairMembershipFormula]
  rfl

theorem realize_coinitialBelowFormula (M : TransitiveGround.{u}) {n}
    (order F target B : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (coinitialBelowFormula order F target B).toFormula env ↔
      CoinitialBelowCode (env order) (env F) (env target) (env B) :=
  (realize_toFormula M _ env members).trans
    (truth_coinitialBelowFormula order F target B env)

end BoundedFormula

end



end PartitionPilot.Forcing

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_FixedTopCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

universe u

namespace MeetOrderCode

theorem eq_canonicalMeetGraph {L r μ : ZFSet.{u}} (code : MeetOrderCode L r μ) :
    μ = canonicalMeetGraph L r := by
  apply ZFSet.ext
  intro v
  constructor
  · intro hv
    obtain ⟨a, ha, z, _, rfl⟩ := ZFSet.mem_prod.1 (code.operation.1 hv)
    obtain ⟨x, _, y, _, rfl⟩ := ZFSet.mem_prod.1 ha
    exact (pair_mem_canonicalMeetGraph L r x y z).2 (code.pair_iff.1 hv)
  · intro hv
    obtain ⟨x, hx, y, hy, z, hz, rfl, h⟩ := (mem_canonicalMeetGraph L r v).1 hv
    exact code.pair_iff.2 ⟨hx, hy, hz, h⟩

end MeetOrderCode

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundPrincipalNiceSupportCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u}
variable [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation I)
variable (T : ZFSet.{u}) (K : I → Subgroup G)

theorem pair_mem_niceSupportRelation (i : I) (tau : ZFSet.{u}) :
    ZFSet.pair (b.encode i) tau ∈ M.niceSupportRelation a s b T K ↔
      tau ∈ M.sets ∧ NiceNameCode a s T (K i) tau := by
  rw [niceSupportRelation, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, j, sigma, eq, candidate⟩
    obtain ⟨keys, rfl⟩ := ZFSet.pair_inj.1 eq
    have same := b.injective keys
    subst j
    exact (M.mem_niceNameCandidates a s T (K i) tau).1 candidate
  · intro code
    exact ⟨ZFSet.pair_mem_prod.2 ⟨b.encode_mem i,
      (M.mem_niceSupportNameCodes a s T K tau).2 ⟨code.1, i, code.2⟩⟩,
      i, tau, rfl, (M.mem_niceNameCandidates a s T (K i) tau).2 code⟩

end PartitionPilot.Forcing.TransitiveGround



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundQuantifiedGraphFormulas
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

theorem realize_allGraphFields {n} (graph : Fin n) (body : SetFormula (n + 2))
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (allGraphFields graph body) env ↔
      ∀ x y, ZFSet.pair x y ∈ env graph →
        Realize M.sets body (extend y (extend x env)) := by
  simp only [allGraphFields, Realize, realize_imp]
  constructor
  · intro holds x y entry
    have pairGround := M.transitive (members graph) entry
    have hx := M.pair_left pairGround
    have hy := M.pair_right pairGround
    exact holds x hx y hy ((BoundedFormula.realize_toFormula M _ _
      (Fin.cases hy (Fin.cases hx members))).2
        ((BoundedFormula.truth_pairMembershipFormula _ _ _ _).2 entry))
  · intro holds x hx y hy entry
    exact holds x y ((BoundedFormula.truth_pairMembershipFormula _ _ _ _).1
      ((BoundedFormula.realize_toFormula M _ _ (Fin.cases hy (Fin.cases hx members))).1 entry))

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

theorem realize_meetFilterFormula (M : TransitiveGround.{u}) {n}
    (P r μ F : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) (meet : MeetOrderCode (env P) (env r) (env μ)) :
    Realize M.sets (meetFilterFormula P r μ F).toFormula env ↔
      MeetFilterCode (env P) (env r) (env μ) (env F) :=
  (realize_toFormula M _ env members).trans (truth_meetFilterFormula P r μ F env meet)

end BoundedFormula

universe u

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundSerialOrbits
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
variable (M : TransitiveGround.{u})

theorem exists_groundSerialOrbit
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {W R initial : ZFSet.{u}} (hW : W ∈ M.sets) (hR : R ∈ M.sets)
    (hInitial : initial ∈ W)
    (serial : ∀ x ∈ W, ∃ y ∈ W, ZFSet.pair x y ∈ R) :
    ∃ history ∈ M.sets, ZFSet.IsFunc ZFSet.omega W history ∧
      (∀ y, ZFSet.pair ∅ y ∈ history ↔ y = initial) ∧
      ∀ n ∈ ZFSet.omega, ∀ x y,
        ZFSet.pair n x ∈ history → ZFSet.pair (insert n n) y ∈ history → ZFSet.pair x y ∈ R := by
  obtain ⟨step, hStep, function, selected⟩ :=
    M.uniformize_relation pairing unions powers separation choice hW hW hR serial
  let s := SetMembers.presentation W
  let f := s.decodeFunction s step function
  let b := SetMembers.ofMem initial hInitial
  have graphGround : s.graph s f ∈ M.sets :=
    M.decoded_function_graph_mem s s hStep function
  let history := natPresentation.graph s (fun n => natIterate f b n.down)
  have historyGround : history ∈ M.sets :=
    M.natural_recursion_graph_mem pairing unions powers separation infinite s f b hW graphGround
  have historyFunction : ZFSet.IsFunc ZFSet.omega W history := natPresentation.graph_isFunc s _
  have canonical (n : Nat) :
      ZFSet.pair (natSetCode n) (s.encode (natIterate f b n)) ∈ history :=
    (natPresentation.pair_mem_graph s (fun n => natIterate f b n.down) ⟨n⟩ _).2 rfl
  have entryValue (n : Nat) (y : ZFSet.{u})
      (entry : ZFSet.pair (natSetCode n) y ∈ history) : y = s.encode (natIterate f b n) := by
    obtain ⟨_, _, unique⟩ := historyFunction.2 (natSetCode n) (natSetCode_mem_omega n)
    exact (unique y entry).trans (unique _ (canonical n)).symm
  refine ⟨history, historyGround, historyFunction, ?_, ?_⟩
  · intro y
    constructor
    · intro entry
      exact (entryValue 0 y entry).trans (SetMembers.raw_ofMem initial hInitial)
    · intro equal
      exact equal.symm ▸ (SetMembers.raw_ofMem initial hInitial ▸ canonical 0)
  · intro n hn x y first second
    obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
    have firstValue := entryValue k x first
    have secondValue := entryValue (k + 1) y second
    rw [firstValue, secondValue]
    exact selected (s.decodeFunction_mem s step function (natIterate f b k))

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundRowAssignmentCuts
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
variable (M : TransitiveGround.{u})

theorem realize_rowAssignmentCutFormula {n : Nat} (z levels alpha : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (rowAssignmentCutFormula z levels alpha) env ↔
      ∃ row A, env z = ZFSet.pair (ZFSet.pair row A)
        (ZFSet.pair row (assignmentCut (env levels) (env alpha) A)) := by
  rw [rowAssignmentCutFormula, realize_exBlock]
  have actual (f : Fin 5 → ZFSet.{u}) (ground : ∀ j, f j ∈ M.sets) :
      Realize M.sets (SetFormula.rowAssignmentCutBody z levels alpha).toFormula
        (extendMany 5 f env) ↔
      env z = ZFSet.pair (f 3) (f 4) ∧ f 3 = ZFSet.pair (f 0) (f 1) ∧
        f 4 = ZFSet.pair (f 0) (f 2) ∧
          f 2 = assignmentCut (env levels) (env alpha) (f 1) := by
    rw [BoundedFormula.realize_toFormula M _ _ (extendMany_members 5 f env ground members)]
    simp only [SetFormula.rowAssignmentCutBody, BoundedFormula.Truth,
      BoundedFormula.truth_orderedPairFormula, BoundedFormula.truth_assignmentCutFormula,
      extendMany_prefix, extendMany_suffix]
  constructor
  · rintro ⟨f, ground, body⟩
    obtain ⟨equal, upper, lower, cut⟩ := (actual f ground).1 body
    rw [upper, lower, cut] at equal
    exact ⟨f 0, f 1, equal⟩
  · rintro ⟨row, A, equal⟩
    have pairGround := equal ▸ members z
    have upper := M.pair_left pairGround
    have lower := M.pair_right pairGround
    let cut := assignmentCut (env levels) (env alpha) A
    let f : Fin 5 → ZFSet.{u} := ![row, A, cut, ZFSet.pair row A, ZFSet.pair row cut]
    have ground : ∀ j, f j ∈ M.sets :=
      Fin.cases (M.pair_left upper) (Fin.cases (M.pair_right upper)
        (Fin.cases (M.pair_right lower) (Fin.cases upper
          (Fin.cases lower (fun j => Fin.elim0 j)))))
    exact ⟨f, ground, (actual f ground).2 ⟨equal, rfl, rfl, rfl⟩⟩

theorem rowAssignmentCutGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {upper lower levels alpha : ZFSet.{u}}
    (hUpper : upper ∈ M.sets) (hLower : lower ∈ M.sets)
    (hLevels : levels ∈ M.sets) (hAlpha : alpha ∈ M.sets) :
    rowAssignmentCutGraph upper lower levels alpha ∈ M.sets := by
  let params : Fin 2 → ZFSet.{u} := ![levels, alpha]
  have ground : ∀ j, params j ∈ M.sets :=
    Fin.cases hLevels (Fin.cases hAlpha (fun j => Fin.elim0 j))
  have bound := M.prod_mem pairing unions powers separation hUpper hLower
  have selected := M.separation_mem separation (rowAssignmentCutFormula 0 1 2) params ground bound
  have equal : ZFSet.sep (fun z => Realize M.sets (rowAssignmentCutFormula 0 1 2) (extend z params))
      (ZFSet.prod upper lower) = rowAssignmentCutGraph upper lower levels alpha := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, mem_rowAssignmentCutGraph]
    apply and_congr_right
    intro hz
    exact M.realize_rowAssignmentCutFormula 0 1 2 (extend z params)
      (Fin.cases (M.transitive bound hz) ground)
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing

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



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_preparationForcingFormula {n} (P order q nodes visibility z F f : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (preparationForcingFormula P order q nodes visibility z F f) env ↔
      PreparationForcingCode M (env P) (env order) (env q) (env nodes)
        (env visibility) (env z) (env F) (env f) := by
  rw [preparationForcingFormula, Realize, M.realize_allGraphFields _ _ env members,
    M.realize_allGraphFields _ _ env members]
  simp only [realize_imp, Realize, M.realize_stageOneForcingAt]
  have names (x y : ZFSet.{u}) :
      (fun j : Fin 2 => extend y (extend x env) (![z.succ.succ, 0] j)) = ![env z, y] := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)) j
  simp only [names]
  rfl

end TransitiveGround

end PartitionPilot.Forcing


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundPreparationForcing
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u}
variable [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation I)
variable (K : I → Subgroup G)

omit [OrderTop P] in
private theorem rawForces_pair_iff
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (phi : SetFormula 2) (p : P) (z tau : (M.nameDomain s).names) :
    stageOneRawForces M s.carrier s.conditionOrder (s.encode p) phi ![z.val.val, tau.val.val] ↔
      Forces (M.nameDomain s) phi ![z, tau] p := by
  have fields : (fun j : Fin 2 => (![z, tau] j).val.val) = ![z.val.val, tau.val.val] := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)) j
  have translated := M.stageOneRawForces_iff s pairing unions powers separation collection
    carrier order phi p ![z, tau]
  rw [fields] at translated
  exact translated

theorem preparationForcingCode_iff
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (T N : ZFSet.{u}) (graphGround : M.niceVisibilityGraph a s b T K ∈ M.sets)
    (namesGround : N ∈ M.sets) (valid : ∀ tau ∈ N, IsName s tau)
    (z : (M.nameDomain s).names) (F f : ZFSet.{u})
    (range : f ⊆ ZFSet.prod b.carrier N) (p : P) :
    PreparationForcingCode M s.carrier s.conditionOrder (s.encode p) b.carrier
      (M.niceVisibilityGraph a s b T K) z.val.val F f ↔
      M.DecidesVisibilityProfile a s b K T F z.val p ∧
      ∀ v (tau : Name s), tau.val ∈ N → ZFSet.pair v tau.val ∈ f →
        Name.ForcesEq p z.val tau := by
  let vis (v : I) : (M.nameDomain s).names :=
    ⟨M.niceVisibilityName a s T (K v),
      M.pair_right (M.transitive graphGround
        ((M.pair_mem_niceVisibilityGraph a s b T K v _).2 rfl))⟩
  have memForces (v : I) :
      stageOneRawForces M s.carrier s.conditionOrder (s.encode p)
        (.mem 0 1 : SetFormula 2) ![z.val.val, (vis v).val.val] ↔
        Name.ForcesMem p z.val (vis v).val :=
    rawForces_pair_iff M s pairing unions powers separation collection carrier order
      (.mem 0 1 : SetFormula 2) p z (vis v)
  have negForces (v : I) :
      stageOneRawForces M s.carrier s.conditionOrder (s.encode p)
        (.neg (.mem 0 1) : SetFormula 2) ![z.val.val, (vis v).val.val] ↔
        ∀ q : P, q ≤ p → ¬ Name.ForcesMem q z.val (vis v).val :=
    rawForces_pair_iff M s pairing unions powers separation collection carrier order
      (.neg (.mem 0 1) : SetFormula 2) p z (vis v)
  have eqForces (tau : (M.nameDomain s).names) :
      stageOneRawForces M s.carrier s.conditionOrder (s.encode p)
        (.equal 0 1 : SetFormula 2) ![z.val.val, tau.val.val] ↔
        Name.ForcesEq p z.val tau.val :=
    rawForces_pair_iff M s pairing unions powers separation collection carrier order
      (.equal 0 1 : SetFormula 2) p z tau
  constructor
  · rintro ⟨profile, equalities⟩
    constructor
    · intro v
      have decisions := profile (b.encode v) (vis v).val.val
        ((M.pair_mem_niceVisibilityGraph a s b T K v _).2 rfl) (b.encode_mem v)
      exact ⟨fun yes => (memForces v).1 (decisions.1 yes),
        fun no => (negForces v).1 (decisions.2 no)⟩
    · intro v tau htau entry
      exact (eqForces ⟨tau, M.transitive namesGround htau⟩).1 (equalities v tau.val entry)
  · rintro ⟨profile, equalities⟩
    constructor
    · intro v V entry hv
      obtain ⟨i, rfl⟩ := (b.mem_carrier v).1 hv
      have eq := (M.pair_mem_niceVisibilityGraph a s b T K i V).1 entry
      subst V
      exact ⟨fun yes => (memForces i).2 ((profile i).1 yes),
        fun no => (negForces i).2 ((profile i).2 no)⟩
    · intro v tau entry
      have htau := (ZFSet.pair_mem_prod.1 (range entry)).2
      let name : (M.nameDomain s).names := ⟨⟨tau, valid tau htau⟩, M.transitive namesGround htau⟩
      exact (eqForces name).2 (equalities v name.val htau entry)

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_SupportedCertificateRelations
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PartitionPilot.Forcing
universe u

theorem pair_mem_supportedCertificateRelation
    (J PF PB WF nodes N order R inputEval niceEval visibilityEval j F B f : ZFSet.{u}) :
    ZFSet.pair j (ZFSet.pair F (ZFSet.pair B f)) ∈
        supportedCertificateRelation J PF PB WF nodes N order R inputEval niceEval visibilityEval ↔
      j ∈ J ∧ F ∈ PF ∧ B ∈ PB ∧ f ∈ WF ∧
        ∃ value, ZFSet.pair j value ∈ inputEval ∧
          SupportedEqualityCertificate nodes N order R niceEval visibilityEval value F B f := by
  rw [supportedCertificateRelation, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, j', hj, F', hF, B', hB, f', hf, equal, value, evaluated, certificate⟩
    have outer := ZFSet.pair_inj.1 equal
    have middle := ZFSet.pair_inj.1 outer.2
    have inner := ZFSet.pair_inj.1 middle.2
    cases outer.1
    cases middle.1
    cases inner.1
    cases inner.2
    exact ⟨hj, hF, hB, hf, value, evaluated, certificate⟩
  · rintro ⟨hj, hF, hB, hf, value, evaluated, certificate⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hj, ZFSet.pair_mem_prod.2
      ⟨hF, ZFSet.pair_mem_prod.2 ⟨hB, hf⟩⟩⟩,
      j, hj, F, hF, B, hB, f, hf, rfl, value, evaluated, certificate⟩

end PartitionPilot.Forcing

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_RowAssignmentTransitionFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

namespace BoundedFormula

private theorem truth_cutGraphProductMember {n : Nat} (z upper lower : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (cutGraphProductMember z upper lower) env ↔ env z ∈ ZFSet.prod (env upper) (env lower) := by
  simp only [cutGraphProductMember, truth_exMem, truth_orderedPairFormula]
  constructor
  · rintro ⟨x, hx, y, hy, equal⟩
    change env z = ZFSet.pair x y at equal
    rw [equal]
    exact ZFSet.pair_mem_prod.2 ⟨hx, hy⟩
  · intro hz
    obtain ⟨x, hx, y, hy, equal⟩ := ZFSet.mem_prod.1 hz
    exact ⟨x, hx, y, hy, equal⟩
end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_rowAssignmentCutGraphFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {n : Nat} (output upper lower levels alpha : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (rowAssignmentCutGraphFormula output upper lower levels alpha) env ↔
      env output = rowAssignmentCutGraph (env upper) (env lower) (env levels) (env alpha) := by
  have ground := M.rowAssignmentCutGraph_mem pairing unions powers separation
    (members upper) (members lower) (members levels) (members alpha)
  apply M.realize_exactSetFormula output _ env (members output) (fun _ hz => M.transitive ground hz)
  intro z hz
  have allGround : ∀ j, (extend z env) j ∈ M.sets := Fin.cases hz members
  change (Realize M.sets (BoundedFormula.cutGraphProductMember 0 upper.succ lower.succ).toFormula
      (extend z env) ∧ Realize M.sets (rowAssignmentCutFormula 0 levels.succ alpha.succ)
      (extend z env)) ↔ _
  rw [BoundedFormula.realize_toFormula M _ _ allGround,
    BoundedFormula.truth_cutGraphProductMember,
    M.realize_rowAssignmentCutFormula 0 levels.succ alpha.succ _ allGround]
  exact (mem_rowAssignmentCutGraph _ _ _ _ z).symm

end TransitiveGround

end PartitionPilot.Forcing

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

theorem truth_certificateGraphEntryAt {n} (j F B f k : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (certificateGraphEntryAt j F B f k) env ↔
      ZFSet.pair (env j) (ZFSet.pair (env F) (ZFSet.pair (env B) (env f))) ∈ env k := by
  simp only [certificateGraphEntryAt, truth_exGraphFields, Truth,
    truth_exPairFields, truth_orderedPairFormula]
  change (∃ key certificate, ZFSet.pair key certificate ∈ env k ∧ key = env j ∧
    ∃ profile tail, certificate = ZFSet.pair profile tail ∧ profile = env F ∧
      tail = ZFSet.pair (env B) (env f)) ↔ _
  constructor
  · rintro ⟨key, certificate, entry, rfl, profile, tail, rfl, rfl, rfl⟩
    exact entry
  · intro entry
    exact ⟨env j, _, entry, rfl, env F, _, rfl, rfl, rfl⟩

theorem truth_enumerationGraphEntryAt {n} (j e names g : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (enumerationGraphEntryAt j e names g) env ↔
      ZFSet.pair (env j) (ZFSet.pair (env e) (env names)) ∈ env g := by
  simp only [enumerationGraphEntryAt, truth_exGraphFields, Truth, truth_orderedPairFormula]
  change (∃ key pair, ZFSet.pair key pair ∈ env g ∧ key = env j ∧
    pair = ZFSet.pair (env e) (env names)) ↔ _
  constructor
  · rintro ⟨key, pair, entry, rfl, rfl⟩
    exact entry
  · intro entry
    exact ⟨env j, _, entry, rfl, rfl⟩





end PartitionPilot.Forcing.BoundedFormula

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



namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

theorem truth_visibilitySupportAt {n} (node tau nodes names visibility top : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (visibilitySupportAt node tau nodes names visibility top) env ↔
      ZFSet.pair (env node) (env tau) ∈ visibilitySupportIncidence
        (env nodes) (env names) (env visibility) (env top) := by
  simp only [visibilitySupportAt, Truth, truth_exGraphFields, truth_pairMembershipFormula]
  rw [pair_mem_visibilitySupportIncidence]
  change (env node ∈ env nodes ∧ env tau ∈ env names ∧
    ∃ v V, ZFSet.pair v V ∈ env visibility ∧ v = env node ∧
      ZFSet.pair (env tau) (env top) ∈ V) ↔ _
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨v, V, edge, rfl, member⟩
    exact ⟨V, edge, member⟩
  · rintro ⟨V, edge, member⟩
    exact ⟨env node, V, edge, rfl, member⟩

end PartitionPilot.Forcing.BoundedFormula

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

variable {I G P : Type u} [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation I)
variable (T : ZFSet.{u}) (K : I → Subgroup G)

theorem visibilitySupportIncidence_candidates (v : I) (tau : ZFSet.{u}) :
    ZFSet.pair (b.encode v) tau ∈ visibilitySupportIncidence b.carrier
      (M.groundRelations T s.carrier) (M.niceVisibilityGraph a s b T K) (s.encode ⊤) ↔
      tau ∈ M.sets ∧ NiceNameCode a s T (K v) tau := by
  rw [pair_mem_visibilitySupportIncidence]
  constructor
  · rintro ⟨_, _, V, entry, member⟩
    have equal := (M.pair_mem_niceVisibilityGraph a s b T K v V).1 entry
    rw [equal, M.niceVisibilityName_code] at member
    exact (M.mem_niceNameCandidates a s T (K v) tau).1
      (ZFSet.pair_mem_prod.1 member).1
  · intro code
    have member := (M.mem_niceNameCandidates a s T (K v) tau).2 code
    refine ⟨b.encode_mem v, M.niceNameCandidates_subset a s T (K v) member,
      (M.niceVisibilityName a s T (K v)).val,
      (M.pair_mem_niceVisibilityGraph a s b T K v _).2 rfl, ?_⟩
    rw [M.niceVisibilityName_code]
    exact ZFSet.pair_mem_prod.2 ⟨member, ZFSet.mem_singleton.2 rfl⟩

theorem visibilitySupportIncidence_eq_niceSupportRelation :
    visibilitySupportIncidence b.carrier (M.groundRelations T s.carrier)
      (M.niceVisibilityGraph a s b T K) (s.encode ⊤) =
      M.niceSupportRelation a s b T K := by
  apply ZFSet.ext
  intro z
  constructor
  · intro member
    obtain ⟨v, hv, tau, _, rfl, _⟩ :=
      (mem_visibilitySupportIncidence _ _ _ _ z).1 member
    obtain ⟨i, rfl⟩ := (b.mem_carrier v).1 hv
    exact (M.pair_mem_niceSupportRelation a s b T K i tau).2
      ((M.visibilitySupportIncidence_candidates a s b T K i tau).1 member)
  · intro member
    obtain ⟨_, i, tau, rfl, _⟩ := ZFSet.mem_sep.1 member
    exact (M.visibilitySupportIncidence_candidates a s b T K i tau).2
      ((M.pair_mem_niceSupportRelation a s b T K i tau).1 member)

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_PreparedCertificateCodes
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

theorem truth_synchronizedEnumerationFormula {n} (omega N B f e names : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (synchronizedEnumerationFormula omega N B f e names) env ↔
      SynchronizedEnumerationCode (env omega) (env N) (env B) (env f) (env e) (env names) := by
  simp only [synchronizedEnumerationFormula, Truth, truth_functionFormula,
    truth_exMem, truth_pairMembershipFormula, truth_imp]
  change (ZFSet.IsFunc (env B) (env N) (env f) ∧
    ZFSet.IsFunc (env omega) (env B) (env e) ∧
    ZFSet.IsFunc (env omega) (env N) (env names) ∧
    (∀ v ∈ env B, ∃ n ∈ env omega, ZFSet.pair n v ∈ env e) ∧
    (∀ n ∈ env omega, ∀ v ∈ env B, ∀ tau ∈ env N, ZFSet.pair n v ∈ env e →
      ZFSet.pair n tau ∈ env names → ZFSet.pair v tau ∈ env f) ∧
    (∀ n ∈ env omega, ∀ v ∈ env B, ∀ tau ∈ env N, ZFSet.pair n v ∈ env e →
      ZFSet.pair v tau ∈ env f → ZFSet.pair n tau ∈ env names)) ↔ _
  constructor
  · rintro ⟨ff, ef, nf, onto, forward, backward⟩
    refine ⟨ff, ef, nf, onto, ?_, ?_⟩
    · intro n hn v tau nv nt
      exact forward n hn v (ZFSet.pair_mem_prod.1 (ef.1 nv)).2
        tau (ZFSet.pair_mem_prod.1 (nf.1 nt)).2 nv nt
    · intro n hn v tau nv vt
      exact backward n hn v (ZFSet.pair_mem_prod.1 (ef.1 nv)).2
        tau (ZFSet.pair_mem_prod.1 (ff.1 vt)).2 nv vt
  · rintro ⟨ff, ef, nf, onto, forward, backward⟩
    exact ⟨ff, ef, nf, onto, fun n hn v _ tau _ => forward n hn v tau,
      fun n hn v _ tau _ => backward n hn v tau⟩

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_preparedCertificateFormula {n}
    (P order q nodes nodeOrder meet N visibility top omega z F B f e names : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (meetCode : MeetOrderCode (env nodes) (env nodeOrder) (env meet)) :
    Realize M.sets
      (preparedCertificateFormula P order q nodes nodeOrder meet N visibility top omega z F B f e names) env ↔
      PreparedCertificateCode M (env P) (env order) (env q) (env nodes) (env nodeOrder)
        (env meet) (env N) (env visibility) (env top) (env omega) (env z)
        (env F) (env B) (env f) (env e) (env names) := by
  have nonempty : Realize M.sets (BoundedFormula.exMem B (.equal 0 0)).toFormula env ↔
      (env B).Nonempty := by
    rw [BoundedFormula.realize_toFormula M _ env members, BoundedFormula.truth_exMem]
    simp only [BoundedFormula.Truth, and_true]
    rfl
  have supported : Realize M.sets (allGraphFields f
      (BoundedFormula.visibilitySupportAt 1 0 nodes.succ.succ N.succ.succ
        visibility.succ.succ top.succ.succ).toFormula) env ↔
      ∀ v tau, ZFSet.pair v tau ∈ env f →
        ZFSet.pair v tau ∈ visibilitySupportIncidence (env nodes) (env N) (env visibility) (env top) := by
    rw [M.realize_allGraphFields _ _ env members]
    constructor
    · intro holds v tau entry
      have pairGround := M.transitive (members f) entry
      exact (BoundedFormula.truth_visibilitySupportAt _ _ _ _ _ _ _).1
        ((BoundedFormula.realize_toFormula M _ _
          (Fin.cases (M.pair_right pairGround) (Fin.cases (M.pair_left pairGround) members))).1
            (holds v tau entry))
    · intro holds v tau entry
      have pairGround := M.transitive (members f) entry
      exact (BoundedFormula.realize_toFormula M _ _
        (Fin.cases (M.pair_right pairGround) (Fin.cases (M.pair_left pairGround) members))).2
          ((BoundedFormula.truth_visibilitySupportAt _ _ _ _ _ _ _).2 (holds v tau entry))
  simp only [preparedCertificateFormula, Realize]
  rw [BoundedFormula.realize_meetFilterFormula M _ _ _ _ env members meetCode,
    BoundedFormula.realize_coinitialBelowFormula M _ _ _ _ env members,
    nonempty, BoundedFormula.realize_toFormula M _ env members,
    BoundedFormula.truth_synchronizedEnumerationFormula, supported,
    M.realize_preparationForcingFormula _ _ _ _ _ _ _ _ env members]
  rfl

end TransitiveGround

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

namespace TransitiveGround
open SetRealization
universe u
variable (M : TransitiveGround.{u}) {L G P : Type u}
variable [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L)
variable (T : ZFSet.{u}) (K : L → Subgroup G)

theorem supportedCertificateFamily_groundData (nodeOrder J : ZFSet.{u})
    (validJ : ∀ z ∈ J, IsName s z) (H : ConditionFilter P)
    (j F B f : ZFSet.{u})
    (member : ZFSet.pair j (ZFSet.pair F (ZFSet.pair B f)) ∈
      M.supportedCertificateFamilyRelation a s b T K nodeOrder J validJ H) :
    j ∈ J ∧ F ∈ M.sets ∧ B ∈ M.sets ∧ f ∈ M.sets ∧
      M.groundEmbeddable B ZFSet.omega ∧ F ⊆ b.carrier ∧ B ⊆ F ∧
      (∀ v ∈ F, ∃ w ∈ B, ZFSet.pair w v ∈ nodeOrder) ∧
      ZFSet.IsFunc B (M.niceSupportNameCodes a s T K) f ∧
      ∀ v ∈ B, ∀ tau ∈ M.niceSupportNameCodes a s T K,
        ZFSet.pair v tau ∈ f → ZFSet.pair v tau ∈ M.niceSupportRelation a s b T K := by
  obtain ⟨hj, hF, hB, hf, value, _, certificate⟩ :=
    (pair_mem_supportedCertificateRelation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).1 member
  have small := (M.mem_groundSmallSubsets b.carrier ZFSet.omega B).1 hB
  exact ⟨hj, ((M.mem_groundPower b.carrier F).1 hF).1, small.1,
    ((M.mem_groundRelations b.carrier (M.niceSupportNameCodes a s T K) f).1 hf).1,
    small.2.2, certificate.1, certificate.2.1, certificate.2.2.1,
    certificate.2.2.2.1, fun v hv tau ht edge => (certificate.2.2.2.2.2 v hv tau ht edge).1⟩

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

section
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_preparedCertificateFamilyFormula {n}
    (P order q nodes nodeOrder meet N visibility top omega J C E k enumerations : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (meetCode : MeetOrderCode (env nodes) (env nodeOrder) (env meet)) :
    Realize M.sets
      (preparedCertificateFamilyFormula P order q nodes nodeOrder meet N visibility top omega J C E k enumerations) env ↔
      PreparedCertificateFamilyCode M (env P) (env order) (env q) (env nodes) (env nodeOrder)
        (env meet) (env N) (env visibility) (env top) (env omega) (env J)
        (env C) (env E) (env k) (env enumerations) := by
  have entries : Realize M.sets
      (SetFormula.preparedFamilyEntries P order q nodes nodeOrder meet N visibility top omega k enumerations) env ↔
      ∀ z F B f e names, ZFSet.pair z (ZFSet.pair F (ZFSet.pair B f)) ∈ env k →
        ZFSet.pair z (ZFSet.pair e names) ∈ env enumerations →
        PreparedCertificateCode M (env P) (env order) (env q) (env nodes) (env nodeOrder)
          (env meet) (env N) (env visibility) (env top) (env omega) z F B f e names := by
    let body := SetFormula.imp
      (.conj (BoundedFormula.certificateGraphEntryAt 5 4 3 2 k.succ.succ.succ.succ.succ.succ).toFormula
        (BoundedFormula.enumerationGraphEntryAt 5 1 0 enumerations.succ.succ.succ.succ.succ.succ).toFormula)
      (preparedCertificateFormula P.succ.succ.succ.succ.succ.succ order.succ.succ.succ.succ.succ.succ
        q.succ.succ.succ.succ.succ.succ nodes.succ.succ.succ.succ.succ.succ
        nodeOrder.succ.succ.succ.succ.succ.succ meet.succ.succ.succ.succ.succ.succ
        N.succ.succ.succ.succ.succ.succ visibility.succ.succ.succ.succ.succ.succ
        top.succ.succ.succ.succ.succ.succ omega.succ.succ.succ.succ.succ.succ 5 4 3 2 1 0)
    have meaning (z F B f e names : ZFSet.{u})
        (hz : z ∈ M.sets) (hF : F ∈ M.sets) (hB : B ∈ M.sets)
        (hf : f ∈ M.sets) (he : e ∈ M.sets) (hn : names ∈ M.sets) :
        Realize M.sets body (extend names (extend e (extend f (extend B (extend F (extend z env)))))) ↔
        (ZFSet.pair z (ZFSet.pair F (ZFSet.pair B f)) ∈ env k ∧
          ZFSet.pair z (ZFSet.pair e names) ∈ env enumerations →
          PreparedCertificateCode M (env P) (env order) (env q) (env nodes) (env nodeOrder)
            (env meet) (env N) (env visibility) (env top) (env omega) z F B f e names) := by
      have extended : ∀ i, (extend names (extend e (extend f (extend B (extend F (extend z env)))))) i ∈ M.sets := Fin.cases hn (Fin.cases he (Fin.cases hf
        (Fin.cases hB (Fin.cases hF (Fin.cases hz members)))))
      dsimp only [body]
      rw [realize_imp, Realize, BoundedFormula.realize_toFormula M _ _ extended,
        BoundedFormula.truth_certificateGraphEntryAt, BoundedFormula.realize_toFormula M _ _ extended,
        BoundedFormula.truth_enumerationGraphEntryAt,
        M.realize_preparedCertificateFormula
          P.succ.succ.succ.succ.succ.succ order.succ.succ.succ.succ.succ.succ
          q.succ.succ.succ.succ.succ.succ nodes.succ.succ.succ.succ.succ.succ
          nodeOrder.succ.succ.succ.succ.succ.succ meet.succ.succ.succ.succ.succ.succ
          N.succ.succ.succ.succ.succ.succ visibility.succ.succ.succ.succ.succ.succ
          top.succ.succ.succ.succ.succ.succ omega.succ.succ.succ.succ.succ.succ
          5 4 3 2 1 0 _ extended meetCode]
      rfl
    change (∀ z ∈ M.sets, ∀ F ∈ M.sets, ∀ B ∈ M.sets, ∀ f ∈ M.sets,
      ∀ e ∈ M.sets, ∀ names ∈ M.sets,
      Realize M.sets body (extend names (extend e (extend f (extend B (extend F (extend z env))))))) ↔ _
    constructor
    · intro holds z F B f e names stored enumerated
      have kc := M.pair_right (M.transitive (members k) stored)
      have ec := M.pair_right (M.transitive (members enumerations) enumerated)
      have hz := M.pair_left (M.transitive (members k) stored)
      have hF := M.pair_left kc
      have hB := M.pair_left (M.pair_right kc)
      have hf := M.pair_right (M.pair_right kc)
      have he := M.pair_left ec
      have hn := M.pair_right ec
      exact (meaning z F B f e names hz hF hB hf he hn).1
        (holds z hz F hF B hB f hf e he names hn) ⟨stored, enumerated⟩
    · intro holds z hz F hF B hB f hf e he names hn
      exact (meaning z F B f e names hz hF hB hf he hn).2
        (fun h => holds z F B f e names h.1 h.2)
  simp only [preparedCertificateFamilyFormula, Realize]
  rw [BoundedFormula.realize_toFormula M _ env members, BoundedFormula.truth_functionFormula,
    BoundedFormula.realize_toFormula M _ env members, BoundedFormula.truth_functionFormula, entries]
  rfl

end TransitiveGround

end

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

theorem groundRelations_mono {A B C D : ZFSet.{u}} (left : A ⊆ C) (right : B ⊆ D) :
    M.groundRelations A B ⊆ M.groundRelations C D := by
  intro f member
  obtain ⟨ground, shape⟩ := (M.mem_groundRelations A B f).1 member
  refine (M.mem_groundRelations C D f).2 ⟨ground, ?_⟩
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := ZFSet.mem_prod.1 (shape hz)
  exact ZFSet.pair_mem_prod.2 ⟨left ha, right hb⟩

theorem supportedEqualityCertificateBound_mono {nodes N W : ZFSet.{u}} (inside : N ⊆ W) :
    M.supportedEqualityCertificateBound nodes N ⊆ M.supportedEqualityCertificateBound nodes W := by
  intro z hz
  obtain ⟨F, hF, tail, htail, rfl⟩ := ZFSet.mem_prod.1 hz
  obtain ⟨B, hB, f, hf, rfl⟩ := ZFSet.mem_prod.1 htail
  exact ZFSet.pair_mem_prod.2 ⟨hF, ZFSet.pair_mem_prod.2
    ⟨hB, M.groundRelations_mono (fun _ h => h) inside hf⟩⟩

theorem synchronizedEnumerationBound_mono {nodes N W : ZFSet.{u}} (inside : N ⊆ W) :
    M.synchronizedEnumerationBound nodes N ⊆ M.synchronizedEnumerationBound nodes W := by
  intro z hz
  obtain ⟨e, he, names, hn, rfl⟩ := ZFSet.mem_prod.1 hz
  exact ZFSet.pair_mem_prod.2 ⟨he, M.groundRelations_mono (fun _ h => h) inside hn⟩

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

theorem preparationWitness_mem_of_local {nodes T Q J N r k enumerations : ZFSet.{u}}
    (requestBound : J ⊆ M.groundRelations T Q) (nameBound : N ⊆ M.groundRelations T Q)
    (hr : r ∈ Q) (hk : k ∈ M.sets) (he : enumerations ∈ M.sets)
    (certificates : ZFSet.IsFunc J (M.supportedEqualityCertificateBound nodes N) k)
    (enumerated : ZFSet.IsFunc J (M.synchronizedEnumerationBound nodes N) enumerations) :
    ZFSet.pair r (ZFSet.pair k enumerations) ∈ M.preparationWitnessBound nodes T Q := by
  have localK := (M.mem_groundRelations J (M.supportedEqualityCertificateBound nodes N) k).2
    ⟨hk, certificates.1⟩
  have localE := (M.mem_groundRelations J (M.synchronizedEnumerationBound nodes N) enumerations).2
    ⟨he, enumerated.1⟩
  exact (M.mem_preparationWitnessBound nodes T Q r k enumerations).2
    ⟨hr, M.groundRelations_mono requestBound (M.supportedEqualityCertificateBound_mono nameBound) localK,
      M.groundRelations_mono requestBound (M.synchronizedEnumerationBound_mono nameBound) localE⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u}
variable [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (T : ZFSet.{u}) (K : I → Subgroup G)

theorem niceSupportNameCodes_subset_groundRelations {Q : ZFSet.{u}} (carrier : s.carrier ⊆ Q) :
    M.niceSupportNameCodes a s T K ⊆ M.groundRelations T Q := by
  intro z member
  obtain ⟨ground, i, code⟩ := (M.mem_niceSupportNameCodes a s T K z).1 member
  have localBound := (M.mem_groundRelations T s.carrier z).2 ⟨ground, niceNameCode_subset a s code⟩
  exact M.groundRelations_mono (fun _ h => h) carrier localBound

theorem nicePreparationWitness_mem {nodes Q J r k enumerations : ZFSet.{u}}
    (carrier : s.carrier ⊆ Q) (requests : J ⊆ M.groundRelations T s.carrier)
    (hr : r ∈ Q) (hk : k ∈ M.sets) (he : enumerations ∈ M.sets)
    (certificates : ZFSet.IsFunc J
      (M.supportedEqualityCertificateBound nodes (M.niceSupportNameCodes a s T K)) k)
    (enumerated : ZFSet.IsFunc J
      (M.synchronizedEnumerationBound nodes (M.niceSupportNameCodes a s T K)) enumerations) :
    ZFSet.pair r (ZFSet.pair k enumerations) ∈ M.preparationWitnessBound nodes T Q :=
  M.preparationWitness_mem_of_local
    (fun _ h => M.groundRelations_mono (fun _ h => h) carrier (requests h))
    (M.niceSupportNameCodes_subset_groundRelations a s T K carrier)
    hr hk he certificates enumerated

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

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

theorem realize_storedPreparationFormula {n}
    (p y upperOrder cutGraph meet omega C E : Fin n) (fields : Fin 15 → Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (meetCode : MeetOrderCode (env (fields 10)) (env (fields 11)) (env meet)) :
    Realize M.sets (M.storedPreparationFormula pairing unions powers separation
      p y upperOrder cutGraph meet omega C E fields) env ↔
    M.StoredPreparationCode (env upperOrder) (env cutGraph) (env meet) (env omega)
      (env C) (env E) (fun j => env (fields j)) (env p) (env y) := by
  unfold storedPreparationFormula
  rw [realize_exBlock]
  have actual (w : Fin 8 → ZFSet.{u}) (ground : ∀ j, w j ∈ M.sets) :
      Realize M.sets (transitionBody M pairing unions powers separation
        p y upperOrder cutGraph meet omega C E fields) (extendMany 8 w env) ↔
      (env p = ZFSet.pair (w 0) (w 1) ∧ env y = ZFSet.pair (w 2) (w 5) ∧
        w 5 = ZFSet.pair (w 3) (w 4) ∧ ZFSet.pair (w 2) (env p) ∈ env upperOrder ∧
        ZFSet.pair (w 2) (w 6) ∈ env cutGraph) ∧
      w 7 = M.storedPreparationRequests (w 1) (fun j => env (fields j)) ∧
      PreparedCertificateFamilyCode M (env (fields 7)) (env (fields 8)) (w 6)
        (env (fields 10)) (env (fields 11)) (env meet) (env (fields 14))
        (env (fields 13)) (env (fields 9)) (env omega) (w 7) (env C) (env E) (w 3) (w 4) := by
    have allGround := extendMany_members 8 w env ground members
    dsimp only [transitionBody]
    rw [Realize, Realize, BoundedFormula.realize_toFormula M _ _ allGround]
    have request : Realize M.sets (SetFormula.reindex
        (extend (prefixIndex n 8 7) (extend (prefixIndex n 8 1)
          (fun j => suffixIndex n 8 (fields j))))
        (M.definable_storedPreparationRequests pairing unions powers separation).formula)
        (extendMany 8 w env) ↔
        w 7 = M.storedPreparationRequests (w 1) (fun j => env (fields j)) := by
      rw [realize_reindex, map_extend, map_extend]
      simp only [extendMany_prefix, extendMany_suffix]
      exact (M.definable_storedPreparationRequests pairing unions powers separation).correct
        (extend (w 1) (fun j => env (fields j)))
        (Fin.cases (ground 1) (fun j => members (fields j))) (w 7) (ground 7)
    rw [request, M.realize_preparedCertificateFamilyFormula _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _ allGround (by simpa only [extendMany_suffix] using meetCode)]
    simp only [transitionShape, BoundedFormula.Truth, BoundedFormula.truth_orderedPairFormula,
      BoundedFormula.truth_pairMembershipFormula, extendMany_prefix, extendMany_suffix]
  constructor
  · rintro ⟨w, ground, body⟩
    obtain ⟨⟨input, output, tail, below, cut⟩, requests, prepared⟩ := (actual w ground).1 body
    exact ⟨w 0, w 1, w 2, w 3, w 4, w 6, input, tail ▸ output, below, cut, requests ▸ prepared⟩
  · rintro ⟨row, A, r, k, enumerations, q, input, output, below, cut, prepared⟩
    have hp := input ▸ members p
    have hy := output ▸ members y
    have hTail := M.pair_right hy
    have hq := M.pair_right (M.transitive (members cutGraph) cut)
    let J := M.storedPreparationRequests A (fun j => env (fields j))
    have hJ := M.storedPreparationRequests_mem pairing unions powers separation (M.pair_right hp)
      (fun j => env (fields j)) (fun j => members (fields j))
    let w : Fin 8 → ZFSet.{u} := ![row, A, r, k, enumerations, ZFSet.pair k enumerations, q, J]
    have ground : ∀ j, w j ∈ M.sets := Fin.cases (M.pair_left hp)
      (Fin.cases (M.pair_right hp) (Fin.cases (M.pair_left hy)
        (Fin.cases (M.pair_left hTail) (Fin.cases (M.pair_right hTail)
          (Fin.cases hTail (Fin.cases hq (Fin.cases hJ (fun j => Fin.elim0 j))))))))
    exact ⟨w, ground, (actual w ground).2 ⟨⟨input, output, rfl, below, cut⟩, rfl, prepared⟩⟩

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem pair_mem_storedPreparationRelation
    (Q upperOrder nodes T levels alpha meet : ZFSet.{u}) (fields : Fin 15 → ZFSet.{u})
    (p y : ZFSet.{u}) :
    ZFSet.pair p y ∈ M.storedPreparationRelation Q upperOrder nodes T levels alpha meet fields ↔
    p ∈ Q ∧ y ∈ M.preparationWitnessBound nodes T Q ∧
      M.StoredPreparationCode upperOrder (rowAssignmentCutGraph Q (fields 7) levels alpha)
        meet ZFSet.omega (M.supportedEqualityCertificateBound nodes (M.groundRelations T Q))
        (M.synchronizedEnumerationBound nodes (M.groundRelations T Q)) fields p y := by
  rw [storedPreparationRelation, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hp, hy⟩, p', y', eq, code⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hp, hy, code⟩
  · rintro ⟨hp, hy, code⟩
    exact ⟨⟨hp, hy⟩, p, y, rfl, code⟩

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

private theorem realize_preparationEntryFormula {n}
    (z upperOrder cutGraph meet omega C E : Fin n) (fields : Fin 15 → Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (meetCode : MeetOrderCode (env (fields 10)) (env (fields 11)) (env meet)) :
    Realize M.sets (preparationEntryFormula M pairing unions powers separation
      z upperOrder cutGraph meet omega C E fields) env ↔
      ∃ p y, env z = ZFSet.pair p y ∧
        M.StoredPreparationCode (env upperOrder) (env cutGraph) (env meet) (env omega)
          (env C) (env E) (fun j => env (fields j)) p y := by
  unfold preparationEntryFormula
  rw [realize_exBlock]
  have actual (w : Fin 2 → ZFSet.{u}) (ground : ∀ j, w j ∈ M.sets) :
      Realize M.sets (.conj
        (BoundedFormula.orderedPairFormula (suffixIndex n 2 z)
          (prefixIndex n 2 0) (prefixIndex n 2 1)).toFormula
        (M.storedPreparationFormula pairing unions powers separation
          (prefixIndex n 2 0) (prefixIndex n 2 1) (suffixIndex n 2 upperOrder)
          (suffixIndex n 2 cutGraph) (suffixIndex n 2 meet) (suffixIndex n 2 omega)
          (suffixIndex n 2 C) (suffixIndex n 2 E) (fun j => suffixIndex n 2 (fields j))))
        (extendMany 2 w env) ↔
      env z = ZFSet.pair (w 0) (w 1) ∧
        M.StoredPreparationCode (env upperOrder) (env cutGraph) (env meet) (env omega)
          (env C) (env E) (fun j => env (fields j)) (w 0) (w 1) := by
    have allGround := extendMany_members 2 w env ground members
    rw [Realize, BoundedFormula.realize_toFormula M _ _ allGround,
      BoundedFormula.truth_orderedPairFormula,
      M.realize_storedPreparationFormula pairing unions powers separation
        _ _ _ _ _ _ _ _ _ _ allGround (by simpa only [extendMany_suffix] using meetCode)]
    simp only [extendMany_prefix, extendMany_suffix]
  constructor
  · rintro ⟨w, ground, body⟩
    exact ⟨w 0, w 1, (actual w ground).1 body⟩
  · rintro ⟨p, y, equal, code⟩
    have hp := M.pair_left (equal ▸ members z)
    have hy := M.pair_right (equal ▸ members z)
    exact ⟨![p, y], Fin.cases hp (Fin.cases hy (fun j => Fin.elim0 j)),
      (actual ![p, y] (Fin.cases hp (Fin.cases hy (fun j => Fin.elim0 j)))).2 ⟨equal, code⟩⟩

include pairing unions powers separation in
theorem storedPreparationRelation_mem
    {Q upperOrder nodes T levels alpha meet : ZFSet.{u}}
    (hQ : Q ∈ M.sets) (hOrder : upperOrder ∈ M.sets) (hNodes : nodes ∈ M.sets)
    (hT : T ∈ M.sets) (hLevels : levels ∈ M.sets) (hAlpha : alpha ∈ M.sets)
    (hMeet : meet ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
    (fields : Fin 15 → ZFSet.{u}) (members : ∀ j, fields j ∈ M.sets)
    (meetCode : MeetOrderCode (fields 10) (fields 11) meet) :
    M.storedPreparationRelation Q upperOrder nodes T levels alpha meet fields ∈ M.sets := by
  let W := M.groundRelations T Q
  let C := M.supportedEqualityCertificateBound nodes W
  let E := M.synchronizedEnumerationBound nodes W
  let cut := rowAssignmentCutGraph Q (fields 7) levels alpha
  have hW := M.groundRelations_mem pairing unions powers separation hT hQ
  have hC := M.supportedEqualityCertificateBound_mem pairing unions powers separation hNodes hW omega
  have hE := M.synchronizedEnumerationBound_mem pairing unions powers separation hNodes hW omega
  have hCut := M.rowAssignmentCutGraph_mem pairing unions powers separation hQ (members 7) hLevels hAlpha
  let params : Fin 21 → ZFSet.{u} :=
    extend upperOrder (extend cut (extend meet (extend ZFSet.omega (extend C (extend E fields)))))
  have ground : ∀ j, params j ∈ M.sets := Fin.cases hOrder (Fin.cases hCut
    (Fin.cases hMeet (Fin.cases omega (Fin.cases hC (Fin.cases hE members)))))
  let slots : Fin 15 → Fin 22 := fun j => j.succ.succ.succ.succ.succ.succ.succ
  let formula := preparationEntryFormula M pairing unions powers separation 0 1 2 3 4 5 6 slots
  have bound := M.prod_mem pairing unions powers separation hQ
    (M.preparationWitnessBound_mem pairing unions powers separation hNodes hT hQ omega)
  have selected := M.separation_mem separation formula params ground bound
  have equal : ZFSet.sep (fun z => Realize M.sets formula (extend z params))
      (ZFSet.prod Q (M.preparationWitnessBound nodes T Q)) =
      M.storedPreparationRelation Q upperOrder nodes T levels alpha meet fields := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, storedPreparationRelation, ZFSet.mem_sep]
    apply and_congr_right
    intro hz
    exact realize_preparationEntryFormula M pairing unions powers separation 0 1 2 3 4 5 6 slots
      (extend z params) (Fin.cases (M.transitive bound hz) ground) meetCode
  exact equal ▸ selected

end PartitionPilot.Forcing.TransitiveGround




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

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

theorem realize_varyingPreparationFormula {n}
    (z packed Q upperOrder nodes T levels omega C E : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (M.varyingPreparationFormula pairing unions powers separation
      z packed Q upperOrder nodes T levels omega C E) env ↔
    M.VaryingPreparationCode (env packed) (env Q) (env upperOrder) (env nodes) (env T)
      (env levels) (env omega) (env C) (env E) (env z) := by
  unfold varyingPreparationFormula
  rw [realize_exBlock]
  let fs := fun w : Fin 22 → ZFSet.{u} => fun j : Fin 15 =>
    w j.succ.succ.succ.succ.succ.succ.succ
  have actual (w : Fin 22 → ZFSet.{u}) (ground : ∀ j, w j ∈ M.sets) :
      Realize M.sets (varyingBody M pairing unions powers separation
        z packed Q upperOrder nodes T levels omega C E) (extendMany 22 w env) ↔
      (env z = ZFSet.pair (w 3) (w 2) ∧ w 3 = ZFSet.pair (w 0) (w 1) ∧
        w 4 = refinementFormulaDataCode (fs w) ∧ ZFSet.pair (w 0) (w 4) ∈ env packed ∧
        fs w 6 = env T ∧ fs w 10 = env nodes) ∧
      MeetOrderCode (fs w 10) (fs w 11) (w 5) ∧
      w 6 = rowAssignmentCutGraph (env Q) (fs w 7) (env levels) (w 0) ∧
      M.StoredPreparationCode (env upperOrder) (w 6) (w 5) (env omega)
        (env C) (env E) (fs w) (w 1) (w 2) := by
    have allGround := extendMany_members 22 w env ground members
    dsimp only [varyingBody]
    rw [Realize, Realize, Realize,
      BoundedFormula.realize_toFormula M _ _ allGround,
      BoundedFormula.realize_toFormula M _ _ allGround,
      BoundedFormula.truth_meetOrderFormula,
      M.realize_rowAssignmentCutGraphFormula pairing unions powers separation _ _ _ _ _ _ allGround]
    simp only [varyingShape, BoundedFormula.Truth, BoundedFormula.truth_orderedPairFormula,
      BoundedFormula.truth_nonemptyTupleFormula, BoundedFormula.truth_pairMembershipFormula,
      extendMany_prefix, extendMany_suffix]
    apply and_congr_right
    intro _shape
    apply and_congr_right
    intro meet
    apply and_congr_right
    intro _cut
    simpa only [extendMany_prefix, extendMany_suffix] using
      (M.realize_storedPreparationFormula pairing unions powers separation
        (prefixIndex n 22 1) (prefixIndex n 22 2) (suffixIndex n 22 upperOrder)
        (prefixIndex n 22 6) (prefixIndex n 22 5) (suffixIndex n 22 omega)
        (suffixIndex n 22 C) (suffixIndex n 22 E)
        (fun j : Fin 15 => prefixIndex n 22 j.succ.succ.succ.succ.succ.succ.succ)
        (extendMany 22 w env) allGround (by simpa only [extendMany_prefix] using meet))
  constructor
  · rintro ⟨w, ground, body⟩
    obtain ⟨⟨outer, input, tuple, stored, terms, nodesEq⟩, meet, cut, prepared⟩ :=
      (actual w ground).1 body
    have canonical := meet.eq_canonicalMeetGraph
    refine ⟨w 0, w 1, w 2, fs w, input ▸ outer, tuple ▸ stored, terms, nodesEq,
      canonical ▸ meet, ?_⟩
    rw [canonical, cut] at prepared
    exact prepared
  · rintro ⟨alpha, p, y, fields, outer, stored, terms, nodesEq, meet, prepared⟩
    have hInput := M.pair_left (outer ▸ members z)
    have hAlpha := M.pair_left hInput
    have hp := M.pair_right hInput
    have hy := M.pair_right (outer ▸ members z)
    have hRecord := M.pair_right (M.transitive (members packed) stored)
    have hFields := M.refinementFormulaDataCode_fields_mem fields hRecord
    let mu := canonicalMeetGraph (fields 10) (fields 11)
    let cut := rowAssignmentCutGraph (env Q) (fields 7) (env levels) alpha
    have hMu := M.canonicalMeetGraph_mem pairing unions powers separation (hFields 10) (hFields 11)
    have hCut := M.rowAssignmentCutGraph_mem pairing unions powers separation
      (members Q) (hFields 7) (members levels) hAlpha
    let w : Fin 22 → ZFSet.{u} := extend alpha (extend p (extend y
      (extend (ZFSet.pair alpha p) (extend (refinementFormulaDataCode fields)
        (extend mu (extend cut fields))))))
    have ground : ∀ j, w j ∈ M.sets := Fin.cases hAlpha (Fin.cases hp (Fin.cases hy
      (Fin.cases hInput (Fin.cases hRecord (Fin.cases hMu (Fin.cases hCut hFields))))))
    exact ⟨w, ground, (actual w ground).2
      ⟨⟨outer, rfl, rfl, stored, terms, nodesEq⟩, meet, rfl, prepared⟩⟩

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

include M in
 theorem varyingPreparationRelation_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {stages packed Q upperOrder nodes T : ZFSet.{u}}
    (hStages : stages ∈ M.sets) (hPacked : packed ∈ M.sets)
    (hQ : Q ∈ M.sets) (hOrder : upperOrder ∈ M.sets)
    (hNodes : nodes ∈ M.sets) (hT : T ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) :
    M.varyingPreparationRelation stages packed Q upperOrder nodes T ∈ M.sets := by
  let W := M.groundRelations T Q
  let C := M.supportedEqualityCertificateBound nodes W
  let E := M.synchronizedEnumerationBound nodes W
  let levels := refinementDataHistoryLevels stages packed T
  have hW := M.groundRelations_mem pairing unions powers separation hT hQ
  have hC := M.supportedEqualityCertificateBound_mem pairing unions powers separation hNodes hW omega
  have hE := M.synchronizedEnumerationBound_mem pairing unions powers separation hNodes hW omega
  have hLevels := M.refinementDataHistoryLevels_mem pairing unions powers separation hStages hPacked hT
  let params : Fin 9 → ZFSet.{u} := ![packed, Q, upperOrder, nodes, T, levels, ZFSet.omega, C, E]
  have ground : ∀ j, params j ∈ M.sets := Fin.cases hPacked (Fin.cases hQ
    (Fin.cases hOrder (Fin.cases hNodes (Fin.cases hT (Fin.cases hLevels
      (Fin.cases omega (Fin.cases hC (Fin.cases hE (fun j => Fin.elim0 j)))))))))
  let formula : SetFormula 10 :=
    M.varyingPreparationFormula pairing unions powers separation 0 1 2 3 4 5 6 7 8 9
  have bound := M.prod_mem pairing unions powers separation
    (M.prod_mem pairing unions powers separation hStages hQ)
    (M.preparationWitnessBound_mem pairing unions powers separation hNodes hT hQ omega)
  have selected := M.separation_mem separation formula params ground bound
  have equal : ZFSet.sep (fun z => Realize M.sets formula (extend z params))
      (ZFSet.prod (ZFSet.prod stages Q) (M.preparationWitnessBound nodes T Q)) =
      M.varyingPreparationRelation stages packed Q upperOrder nodes T := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, varyingPreparationRelation, ZFSet.mem_sep]
    apply and_congr_right
    intro hz
    exact M.realize_varyingPreparationFormula pairing unions powers separation
      0 1 2 3 4 5 6 7 8 9 (extend z params) (Fin.cases (M.transitive bound hz) ground)
  exact equal ▸ selected

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundFiniteBirthHistories
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

theorem finiteBirthHistory_extend (k : Nat) {E history e : ZFSet.{u}}
    (function : ZFSet.IsFunc (natSetCode k) E history) (value : e ∈ E) :
    let next := insert (ZFSet.pair (natSetCode k) e) history
    ZFSet.IsFunc (natSetCode (k + 1)) E next ∧ history ⊆ next ∧
      graphRestriction (natSetCode k) next = history ∧
      ∀ y, ZFSet.pair (natSetCode k) y ∈ next ↔ y = e := by
  let graph : FunctionGraphOn (natSetCode k) history := ⟨E, function⟩
  have extended := graph.successor e
  refine ⟨?_, fun _ member => ZFSet.mem_insert_of_mem _ member, ?_, ?_⟩
  · rw [natSetCode_succ]
    refine ⟨?_, extended.to_isFunc.2⟩
    intro z member
    rcases ZFSet.mem_insert_iff.1 member with rfl | member
    · exact ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_insert _ _, value⟩
    · obtain ⟨i, hi, y, hy, rfl⟩ := ZFSet.mem_prod.1 (function.1 member)
      exact ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_insert_of_mem _ hi, hy⟩
  · exact (graphRestriction_insert_of_not_mem (ZFSet.mem_irrefl (natSetCode k))).trans
      graph.restriction_eq
  · intro y
    constructor
    · intro member
      rcases ZFSet.mem_insert_iff.1 member with equal | old
      · exact (ZFSet.pair_inj.1 equal).2
      · exact False.elim (ZFSet.mem_irrefl (natSetCode k) (graph.pair_source old))
    · intro equal
      exact equal.symm ▸ ZFSet.mem_insert _ _

theorem finiteBirthHistory_initial {E e : ZFSet.{u}} (value : e ∈ E) :
    ZFSet.IsFunc (natSetCode 1) E {ZFSet.pair ∅ e} ∧
      ∀ y, ZFSet.pair ∅ y ∈ ({ZFSet.pair ∅ e} : ZFSet.{u}) ↔ y = e := by
  have empty : ZFSet.IsFunc (natSetCode 0) E (∅ : ZFSet.{u}) :=
    ⟨ZFSet.empty_subset _, fun i hi => False.elim (ZFSet.notMem_empty i hi)⟩
  have first := finiteBirthHistory_extend 0 empty value
  exact ⟨first.1, first.2.2.2⟩

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})

theorem finiteBirthHistory_extend_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (k : Nat) {history e : ZFSet.{u}} (ground : history ∈ M.sets) (value : e ∈ M.sets) :
    insert (ZFSet.pair (natSetCode k) e) history ∈ M.sets :=
  M.insert_mem pairing unions
    (M.orderedPair_mem pairing (M.natSetCode_mem separation infinite k) value) ground

theorem finiteBirthHistory_initial_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {e : ZFSet.{u}} (value : e ∈ M.sets) :
    ({ZFSet.pair ∅ e} : ZFSet.{u}) ∈ M.sets := by
  have empty := M.empty_mem ⟨e, value⟩
  have entry := M.orderedPair_mem pairing empty value
  simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing entry entry

end TransitiveGround

end PartitionPilot.Forcing

end

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

theorem birthHistory_scheduled_lookup (k : Nat) {W history : ZFSet.{u}}
    (function : ZFSet.IsFunc (natSetCode (k + 1)) W history) :
    ∃ record ∈ W,
      ZFSet.pair (natSetCode (Nat.unpair k).1) record ∈ history ∧
      ∀ other, ZFSet.pair (natSetCode (Nat.unpair k).1) other ∈ history → other = record := by
  have before : (natSetCode (Nat.unpair k).1 : ZFSet.{u}) ∈ natSetCode (k + 1) :=
    (natSetCode_mem_iff _ _).2 (Nat.lt_succ_of_le (Nat.unpair_left_le k))
  obtain ⟨record, entry, unique⟩ := function.2 _ before
  exact ⟨record, (ZFSet.pair_mem_prod.1 (function.1 entry)).2, entry, unique⟩

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

namespace BoundedFormula
open SetFormula

theorem truth_birthLevelEnumerationFormula {n} (omega stages A levels e : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (birthLevelEnumerationFormula omega stages A levels e) env ↔
      BirthLevelEnumerationCode (env omega) (env stages) (env A) (env levels) (env e) := by
  simp only [birthLevelEnumerationFormula, truth_disj, Truth, truth_emptyFormula,
    truth_functionFormula, truth_imp, truth_exMem, truth_pairMembershipFormula, ← iff_def]
  change (((∀ x ∈ env A, ∀ alpha ∈ env stages, ¬ ZFSet.pair x alpha ∈ env levels) ∧
    env e = ∅) ∨ (ZFSet.IsFunc (env omega) (env stages) (env e) ∧
    ∀ alpha ∈ env stages, (∃ k ∈ env omega, ZFSet.pair k alpha ∈ env e) ↔
      ∃ x ∈ env A, ZFSet.pair x alpha ∈ env levels)) ↔ _
  have empty : (∀ x ∈ env A, ∀ alpha ∈ env stages, ¬ ZFSet.pair x alpha ∈ env levels) ↔
      relationImage (env A) (env stages) (env levels) = ∅ := by
    constructor
    · intro no
      apply ZFSet.ext
      intro alpha
      simp only [mem_relationImage, ZFSet.notMem_empty, iff_false]
      rintro ⟨ha, x, hx, edge⟩
      exact no x hx alpha ha edge
    · intro eq x hx alpha ha edge
      have member := (mem_relationImage (env A) (env stages) (env levels) alpha).2
        ⟨ha, x, hx, edge⟩
      exact ZFSet.notMem_empty alpha (eq ▸ member)
  exact or_congr (and_congr empty Iff.rfl) Iff.rfl

theorem truth_birthLevelEnumerationEntryFormula {n} (entry omega stages levels : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (birthLevelEnumerationEntryFormula entry omega stages levels) env ↔
      ∃ row A e, env entry = ZFSet.pair (ZFSet.pair row A) e ∧
        BirthLevelEnumerationCode (env omega) (env stages) A (env levels) e := by
  simp only [birthLevelEnumerationEntryFormula, truth_exPairFields,
    truth_birthLevelEnumerationFormula]
  change (∃ p e, env entry = ZFSet.pair p e ∧ ∃ row A, p = ZFSet.pair row A ∧
    BirthLevelEnumerationCode (env omega) (env stages) A (env levels) e) ↔ _
  constructor
  · rintro ⟨p, e, eq, row, A, rfl, code⟩
    exact ⟨row, A, e, eq, code⟩
  · rintro ⟨row, A, e, eq, code⟩
    exact ⟨_, e, eq, row, A, rfl, code⟩

end BoundedFormula

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

theorem birthLevelEnumerationRelation_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {Q stages levels : ZFSet.{u}} (hQ : Q ∈ M.sets) (hStages : stages ∈ M.sets)
    (hLevels : levels ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) :
    M.birthLevelEnumerationRelation Q stages levels ∈ M.sets := by
  let params := extend ZFSet.omega (extend stages (extend levels Fin.elim0))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.birthLevelEnumerationEntryFormula 0 1 2 3) params
    (Fin.cases omega (Fin.cases hStages (Fin.cases hLevels (fun i => Fin.elim0 i))))
    (M.prod_mem pairing unions powers separation hQ
      (M.groundRelations_mem pairing unions powers separation omega hStages))
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.birthLevelEnumerationEntryFormula 0 1 2 3) (extend z params))
      (ZFSet.prod Q (M.groundRelations ZFSet.omega stages)) =
      M.birthLevelEnumerationRelation Q stages levels := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, birthLevelEnumerationRelation, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_birthLevelEnumerationEntryFormula 0 1 2 3 _)
  exact equal ▸ selected

theorem exists_refinementBirthLevelEnumerations
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {rows T stages history : ZFSet.{u}} (hRows : rows ∈ M.sets) (hT : T ∈ M.sets)
    (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets)
    (valid : RefinementDataHistory stages history T) :
    let Q := M.refinementHistoryForcing rows T stages history
    let levels := refinementDataHistoryLevels stages history T
    M.birthLevelEnumerationRelation Q stages levels ∈ M.sets ∧
      ∃ selector ∈ M.sets, ZFSet.IsFunc Q (M.groundRelations ZFSet.omega stages) selector ∧
        selector ⊆ M.birthLevelEnumerationRelation Q stages levels ∧
        ∀ row A e, ZFSet.pair (ZFSet.pair row A) e ∈ selector →
          BirthLevelEnumerationCode ZFSet.omega stages A levels e := by
  classical
  dsimp only
  let Q := M.refinementHistoryForcing rows T stages history
  let levels := refinementDataHistoryLevels stages history T
  have omega := M.omega_mem separation infinite
  have hQ := M.refinementHistoryForcing_mem pairing unions powers separation hRows hT hStages hHistory omega
  have hLevels := M.refinementDataHistoryLevels_mem pairing unions powers separation hStages hHistory hT
  have bound := M.groundRelations_mem pairing unions powers separation omega hStages
  have ground := M.birthLevelEnumerationRelation_mem pairing unions powers separation hQ hStages hLevels omega
  have total : ∀ p ∈ Q, ∃ e ∈ M.groundRelations ZFSet.omega stages,
      ZFSet.pair p e ∈ M.birthLevelEnumerationRelation Q stages levels := by
    intro p hp
    have candidate := ((M.mem_refinementHistoryForcing rows T stages history p).1 hp).1
    obtain ⟨row, _, A, hA, _, smallA, rfl⟩ := (M.mem_stageOneCandidateBound _ _ _ p).1 candidate
    have hAttained := M.relationImage_mem separation hA hStages hLevels
    have small := M.groundEmbeddable_function_image pairing unions powers separation choice
      hA hStages omega hLevels valid.levels_function smallA
    by_cases active : (relationImage A stages levels).Nonempty
    · obtain ⟨e, he, function, onto⟩ := M.groundCountable_enumeration
        pairing unions powers separation infinite hAttained active small
      have upperFunction : ZFSet.IsFunc ZFSet.omega stages e := by
        refine ⟨?_, function.2⟩
        intro z hz
        obtain ⟨n, hn, alpha, ha, rfl⟩ := ZFSet.mem_prod.1 (function.1 hz)
        exact ZFSet.pair_mem_prod.2 ⟨hn, ((mem_relationImage A stages levels alpha).1 ha).1⟩
      have heBound := (M.mem_groundRelations ZFSet.omega stages e).2 ⟨he, upperFunction.1⟩
      refine ⟨e, heBound, (M.pair_mem_birthLevelEnumerationRelation Q stages levels row A e).2
        ⟨hp, heBound, Or.inr ⟨upperFunction, ?_⟩⟩⟩
      intro alpha ha
      constructor
      · rintro ⟨n, _, edge⟩
        exact ((mem_relationImage A stages levels alpha).1
          (ZFSet.pair_mem_prod.1 (function.1 edge)).2).2
      · intro witness
        exact onto alpha ((mem_relationImage A stages levels alpha).2 ⟨ha, witness⟩)
    · have empty : relationImage A stages levels = ∅ := by
        apply ZFSet.ext
        intro alpha
        exact ⟨fun ha => False.elim (active ⟨alpha, ha⟩),
          fun ha => False.elim (ZFSet.notMem_empty alpha ha)⟩
      have emptyBound := (M.mem_groundRelations ZFSet.omega stages ∅).2
        ⟨M.empty_mem ⟨stages, hStages⟩, ZFSet.empty_subset _⟩
      exact ⟨∅, emptyBound, (M.pair_mem_birthLevelEnumerationRelation Q stages levels row A ∅).2
        ⟨hp, emptyBound, Or.inl ⟨empty, rfl⟩⟩⟩
  obtain ⟨selector, hs, function, selected⟩ :=
    M.uniformize_relation pairing unions powers separation choice hQ bound ground total
  exact ⟨ground, selector, hs, function, selected, fun row A e entry =>
    ((M.pair_mem_birthLevelEnumerationRelation Q stages levels row A e).1 (selected entry)).2.2⟩

end TransitiveGround

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem birthEnumerationRange_spec
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {Q stages levels selector : ZFSet.{u}} (hQ : Q ∈ M.sets) (hStages : stages ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) (hSelector : selector ∈ M.sets)
    (function : ZFSet.IsFunc Q (M.groundRelations ZFSet.omega stages) selector)
    (selected : selector ⊆ M.birthLevelEnumerationRelation Q stages levels) :
    let E0 := relationImage Q (M.groundRelations ZFSet.omega stages) selector
    E0 ∈ M.sets ∧ E0 ⊆ M.groundRelations ZFSet.omega stages ∧
      (∀ e ∈ E0, e = ∅ ∨ ZFSet.IsFunc ZFSet.omega stages e) ∧
      ∀ row A, ZFSet.pair row A ∈ Q →
        ∃ e ∈ E0, ZFSet.pair (ZFSet.pair row A) e ∈ selector ∧
          BirthLevelEnumerationCode ZFSet.omega stages A levels e := by
  dsimp only
  refine ⟨M.relationImage_mem separation hQ
    (M.groundRelations_mem pairing unions powers separation omega hStages) hSelector,
    fun e he => ((mem_relationImage _ _ _ e).1 he).1, ?_, ?_⟩
  · intro e he
    obtain ⟨_, p, _, edge⟩ := (mem_relationImage _ _ _ e).1 he
    have member := selected edge
    obtain ⟨_, row, A, e', equal, code⟩ := ZFSet.mem_sep.1 member
    obtain ⟨_, rfl⟩ := ZFSet.pair_inj.1 equal
    exact code.elim (fun idle => Or.inl idle.2) (fun active => Or.inr active.1)
  · intro row A hp
    obtain ⟨e, edge, _⟩ := function.2 _ hp
    have bound := (ZFSet.pair_mem_prod.1 (function.1 edge)).2
    exact ⟨e, (mem_relationImage _ _ _ e).2 ⟨bound, _, hp, edge⟩, edge,
      ((M.pair_mem_birthLevelEnumerationRelation Q stages levels row A e).1 (selected edge)).2.2⟩

end TransitiveGround

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


namespace PartitionPilot.Forcing
universe u

namespace BoundedFormula
open SetFormula

theorem truth_exFairStateFields {n} (state : Fin n) (body : BoundedFormula (n + 4))
    (env : Fin n → ZFSet.{u}) :
    Truth (exFairStateFields state body) env ↔
      ∃ n p births last, env state = ZFSet.pair n (ZFSet.pair p (ZFSet.pair births last)) ∧
        Truth body (extend last (extend births (extend p (extend n env)))) := by
  simp only [exFairStateFields, truth_exPairFields, truth_reindex]
  have rearrange (n tail p inner births last : ZFSet.{u}) :
      (fun i => extend last (extend births (extend inner (extend p (extend tail (extend n env)))))
        (Fin.cases 0 (Fin.cases 1 (Fin.cases 3 (Fin.cases 5
          (fun j => j.succ.succ.succ.succ.succ.succ)))) i)) =
        extend last (extend births (extend p (extend n env))) := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.cases ?_
      (fun l => Fin.cases ?_ (fun m => ?_) l) k) j) i <;> rfl
  simp only [rearrange]
  constructor
  · rintro ⟨n, tail, eq, p, inner, rfl, births, last, rfl, holds⟩
    exact ⟨n, p, births, last, eq, holds⟩
  · rintro ⟨n, p, births, last, eq, holds⟩
    exact ⟨n, _, eq, p, _, rfl, births, last, rfl, holds⟩

theorem truth_fairPreparationStateFormula {n} (omega E0 enumSelector state : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (fairPreparationStateFormula omega E0 enumSelector state) env ↔
      FairPreparationStateCode (env omega) (env E0) (env enumSelector) (env state) := by
  simp only [fairPreparationStateFormula, truth_exFairStateFields, Truth, truth_exMem,
    truth_successorFormula, truth_functionFormula, truth_pairMembershipFormula]
  change (∃ n p births last, env state = ZFSet.pair n (ZFSet.pair p (ZFSet.pair births last)) ∧
    n ∈ env omega ∧ ∃ next ∈ env omega, next = insert n n ∧
      ZFSet.IsFunc next (env E0) births ∧ ∃ e ∈ env E0,
        ZFSet.pair p e ∈ env enumSelector ∧ ZFSet.pair n e ∈ births) ↔ _
  constructor
  · rintro ⟨n, p, births, last, shape, hn, next, hm, rfl, function, witness⟩
    exact ⟨n, p, births, last, shape, hn, hm, function, witness⟩
  · rintro ⟨n, p, births, last, shape, hn, hm, function, witness⟩
    exact ⟨n, p, births, last, shape, hn, insert n n, hm, rfl, function, witness⟩

end BoundedFormula






namespace BoundedFormula
open SetFormula

private theorem truth_insertPairFormula {n} (output graph x y : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (insertPairFormula output graph x y) env ↔
      env output = insert (ZFSet.pair (env x) (env y)) (env graph) := by
  simp only [insertPairFormula, Truth, truth_disj, truth_orderedPairFormula,
    truth_subsetFormula, truth_pairMembershipFormula]
  constructor
  · rintro ⟨inside, includes, entry⟩
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_insert_iff]
    exact ⟨fun hz => (inside z hz).symm,
      fun hz => hz.elim (fun eq => eq ▸ entry) (fun hz => includes hz)⟩
  · intro eq
    rw [eq]
    exact ⟨fun z hz => (ZFSet.mem_insert_iff.1 hz).symm,
      fun _ hz => ZFSet.mem_insert_of_mem _ hz, ZFSet.mem_insert _ _⟩

private theorem truth_activePreparationFormula {n}
    (stages U e j p q event prepSelector : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (activePreparationFormula stages U e j p q event prepSelector) env ↔
      ∃ alpha ∈ env stages, ∃ y ∈ env U, (∃ payload, y = ZFSet.pair (env q) payload) ∧
        ZFSet.pair (env j) alpha ∈ env e ∧
        ZFSet.pair (ZFSet.pair alpha (env p)) y ∈ env prepSelector ∧
        env event = ZFSet.pair alpha y := by
  simp only [activePreparationFormula, truth_exMem, truth_exPairFields, Truth,
    truth_pairMembershipFormula, truth_tripleMembershipFormula, truth_orderedPairFormula]
  constructor
  · rintro ⟨alpha, ha, y, hy, q', payload, shape, equal, entry, selected, eventEq⟩
    change q' = env q at equal
    exact ⟨alpha, ha, y, hy, ⟨payload, equal ▸ shape⟩, entry, selected, eventEq⟩
  · rintro ⟨alpha, ha, y, hy, ⟨payload, shape⟩, entry, selected, eventEq⟩
    exact ⟨alpha, ha, y, hy, env q, payload, shape, rfl, entry, selected, eventEq⟩

private theorem truth_fairStepFieldsFormula {arity}
    (omega E0 stages U enumSelector prepSelector gridGraph n p births m q nextBirths event : Fin arity)
    (env : Fin arity → ZFSet.{u}) :
    Truth (fairStepFieldsFormula omega E0 stages U enumSelector prepSelector gridGraph
      n p births m q nextBirths event) env ↔
    env m = insert (env n) (env n) ∧
    ∃ i ∈ env omega, ∃ j ∈ env omega, ∃ e ∈ env E0, ∃ newE ∈ env E0,
      ZFSet.pair (env n) (ZFSet.pair i j) ∈ env gridGraph ∧
      ZFSet.pair i e ∈ env births ∧ ZFSet.pair (env q) newE ∈ env enumSelector ∧
      env nextBirths = insert (ZFSet.pair (env m) newE) (env births) ∧
      ((e = ∅ ∧ env q = env p ∧ env event = ∅) ∨
        (∃ alpha ∈ env stages, ∃ y ∈ env U, (∃ payload, y = ZFSet.pair (env q) payload) ∧
          ZFSet.pair j alpha ∈ e ∧ ZFSet.pair (ZFSet.pair alpha (env p)) y ∈ env prepSelector ∧
          env event = ZFSet.pair alpha y)) := by
  simp only [fairStepFieldsFormula, Truth, truth_successorFormula, truth_exMem,
    truth_rightTripleMembershipFormula, truth_pairMembershipFormula, truth_insertPairFormula,
    truth_disj, truth_emptyFormula, truth_activePreparationFormula]
  rfl

theorem truth_fairPreparationStepFormula {n}
    (omega E0 stages U enumSelector prepSelector gridGraph state next : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (fairPreparationStepFormula omega E0 stages U enumSelector prepSelector gridGraph state next) env ↔
      FairPreparationStepCode (env omega) (env E0) (env stages) (env U) (env enumSelector)
        (env prepSelector) (env gridGraph) (env state) (env next) := by
  simp only [fairPreparationStepFormula, truth_exFairStateFields, truth_fairStepFieldsFormula]
  constructor
  · rintro ⟨n, p, births, last, shape, m, q, nextBirths, event, nextShape, rest⟩
    exact ⟨n, p, births, last, m, q, nextBirths, event, shape, nextShape, rest⟩
  · rintro ⟨n, p, births, last, m, q, nextBirths, event, shape, nextShape, rest⟩
    exact ⟨n, p, births, last, shape, m, q, nextBirths, event, nextShape, rest⟩

end BoundedFormula

end PartitionPilot.Forcing




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem mem_fairPreparationStates (Q stages U E0 enumSelector state : ZFSet.{u}) :
    state ∈ M.fairPreparationStates Q stages U E0 enumSelector ↔
      state ∈ ZFSet.prod ZFSet.omega (ZFSet.prod Q
        (ZFSet.prod (M.groundRelations ZFSet.omega E0) (insert ∅ (ZFSet.prod stages U)))) ∧
      FairPreparationStateCode ZFSet.omega E0 enumSelector state := ZFSet.mem_sep

theorem pair_mem_fairPreparationTransition
    (Q stages U E0 enumSelector prepSelector gridGraph state next : ZFSet.{u}) :
    ZFSet.pair state next ∈ M.fairPreparationTransition Q stages U E0 enumSelector prepSelector gridGraph ↔
      state ∈ M.fairPreparationStates Q stages U E0 enumSelector ∧
      next ∈ M.fairPreparationStates Q stages U E0 enumSelector ∧
      FairPreparationStepCode ZFSet.omega E0 stages U enumSelector prepSelector gridGraph state next := by
  rw [fairPreparationTransition, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hs, hn⟩, state', next', eq, code⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hs, hn, code⟩
  · rintro ⟨hs, hn, code⟩
    exact ⟨⟨hs, hn⟩, state, next, rfl, code⟩

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

include pairing unions powers separation in
theorem fairPreparationStates_mem
    {Q stages U E0 enumSelector : ZFSet.{u}}
    (hQ : Q ∈ M.sets) (hStages : stages ∈ M.sets) (hU : U ∈ M.sets)
    (hE0 : E0 ∈ M.sets) (hEnum : enumSelector ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) :
    M.fairPreparationStates Q stages U E0 enumSelector ∈ M.sets := by
  have history := M.groundRelations_mem pairing unions powers separation omega hE0
  have events := M.insert_mem pairing unions (M.empty_mem ⟨Q, hQ⟩)
    (M.prod_mem pairing unions powers separation hStages hU)
  have bound := M.prod_mem pairing unions powers separation omega
    (M.prod_mem pairing unions powers separation hQ
      (M.prod_mem pairing unions powers separation history events))
  let params : Fin 3 → ZFSet.{u} := ![ZFSet.omega, E0, enumSelector]
  have ground : ∀ j, params j ∈ M.sets := Fin.cases omega
    (Fin.cases hE0 (Fin.cases hEnum (fun j => Fin.elim0 j)))
  let formula : BoundedFormula 4 := BoundedFormula.fairPreparationStateFormula 1 2 3 0
  have selected := M.bounded_separation_mem separation formula params ground bound
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth formula (extend z params))
      (ZFSet.prod ZFSet.omega (ZFSet.prod Q
        (ZFSet.prod (M.groundRelations ZFSet.omega E0) (insert ∅ (ZFSet.prod stages U))))) =
      M.fairPreparationStates Q stages U E0 enumSelector := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, fairPreparationStates, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_fairPreparationStateFormula 1 2 3 0 _)
  exact equal ▸ selected

include pairing unions powers separation in
theorem fairPreparationTransition_mem
    {Q stages U E0 enumSelector prepSelector gridGraph : ZFSet.{u}}
    (hQ : Q ∈ M.sets) (hStages : stages ∈ M.sets) (hU : U ∈ M.sets)
    (hE0 : E0 ∈ M.sets) (hEnum : enumSelector ∈ M.sets)
    (hPrep : prepSelector ∈ M.sets) (hGrid : gridGraph ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) :
    M.fairPreparationTransition Q stages U E0 enumSelector prepSelector gridGraph ∈ M.sets := by
  have states := M.fairPreparationStates_mem pairing unions powers separation hQ hStages hU hE0 hEnum omega
  let params : Fin 7 → ZFSet.{u} := ![ZFSet.omega, E0, stages, U, enumSelector, prepSelector, gridGraph]
  have ground : ∀ j, params j ∈ M.sets := Fin.cases omega (Fin.cases hE0
    (Fin.cases hStages (Fin.cases hU (Fin.cases hEnum (Fin.cases hPrep
      (Fin.cases hGrid (fun j => Fin.elim0 j)))))))
  let formula : BoundedFormula 8 := BoundedFormula.exPairFields 0
    (BoundedFormula.fairPreparationStepFormula 3 4 5 6 7 8 9 1 0)
  have selected := M.bounded_separation_mem separation formula params ground
    (M.prod_mem pairing unions powers separation states states)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth formula (extend z params))
      (ZFSet.prod (M.fairPreparationStates Q stages U E0 enumSelector)
        (M.fairPreparationStates Q stages U E0 enumSelector)) =
      M.fairPreparationTransition Q stages U E0 enumSelector prepSelector gridGraph := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, fairPreparationTransition, ZFSet.mem_sep]
    apply and_congr Iff.rfl
    simp only [formula, BoundedFormula.truth_exPairFields, BoundedFormula.truth_fairPreparationStepFormula]
    rfl
  exact equal ▸ selected

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

private theorem finiteHistory_bound (k : Nat) {E history : ZFSet.{u}}
    (ground : history ∈ M.sets) (function : ZFSet.IsFunc (natSetCode k) E history) :
    history ∈ M.groundRelations ZFSet.omega E := by
  refine (M.mem_groundRelations _ _ _).2 ⟨ground, ?_⟩
  intro z member
  obtain ⟨i, hi, e, he, rfl⟩ := ZFSet.mem_prod.1 (function.1 member)
  obtain ⟨n, _, rfl⟩ := (mem_natSetCode i k).1 hi
  exact ZFSet.pair_mem_prod.2 ⟨natSetCode_mem_omega n, he⟩

theorem exists_fairPreparation_initial
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (stages U : ZFSet.{u}) {Q E0 enumSelector p : ZFSet.{u}}
    (hE0 : E0 ∈ M.sets) (enumerated : ZFSet.IsFunc Q E0 enumSelector) (member : p ∈ Q) :
    ∃ e ∈ E0, ZFSet.pair p e ∈ enumSelector ∧
      ZFSet.pair ∅ (ZFSet.pair p (ZFSet.pair {ZFSet.pair ∅ e} ∅)) ∈
        M.fairPreparationStates Q stages U E0 enumSelector := by
  obtain ⟨e, selected, _⟩ := enumerated.2 p member
  have he := (ZFSet.pair_mem_prod.1 (enumerated.1 selected)).2
  have initial := finiteBirthHistory_initial he
  have historyBound := M.finiteHistory_bound 1
    (M.finiteBirthHistory_initial_mem pairing (M.transitive hE0 he)) initial.1
  refine ⟨e, he, selected, (M.mem_fairPreparationStates _ _ _ _ _ _).2 ⟨?_, ?_⟩⟩
  · exact ZFSet.pair_mem_prod.2 ⟨ZFSet.omega_zero, ZFSet.pair_mem_prod.2
      ⟨member, ZFSet.pair_mem_prod.2 ⟨historyBound, ZFSet.mem_insert _ _⟩⟩⟩
  · exact ⟨∅, p, {ZFSet.pair ∅ e}, ∅, rfl, ZFSet.omega_zero,
      ZFSet.omega_succ ZFSet.omega_zero, initial.1, e, he, selected, (initial.2 e).2 rfl⟩

theorem fairPreparationTransition_serial
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {Q stages U E0 enumSelector prepSelector : ZFSet.{u}}
    (hE0 : E0 ∈ M.sets)
    (enumerated : ZFSet.IsFunc Q E0 enumSelector)
    (enumerationCases : ∀ e ∈ E0, e = ∅ ∨ ZFSet.IsFunc ZFSet.omega stages e)
    (prepared : ZFSet.IsFunc (ZFSet.prod stages Q) U prepSelector)
    (outputs : ∀ y ∈ U, ∃ p ∈ Q, ∃ payload, y = ZFSet.pair p payload) :
    let grid := natPresentation.graph (natPresentation.product natPresentation) omegaGridEquiv
    ∀ state ∈ M.fairPreparationStates Q stages U E0 enumSelector,
      ∃ next ∈ M.fairPreparationStates Q stages U E0 enumSelector,
        ZFSet.pair state next ∈
          M.fairPreparationTransition Q stages U E0 enumSelector prepSelector grid := by
  let grid : ZFSet.{u} := natPresentation.graph (natPresentation.product natPresentation) omegaGridEquiv
  dsimp only
  intro state member
  obtain ⟨bound, n, p, births, last, rfl, hn, _hSucc, birthFunction, _current⟩ :=
    (M.mem_fairPreparationStates _ _ _ _ _ _).1 member
  obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
  have upperParts := (ZFSet.pair_mem_prod.1 bound).2
  have hp := (ZFSet.pair_mem_prod.1 upperParts).1
  have historyBound := (ZFSet.pair_mem_prod.1 (ZFSet.pair_mem_prod.1 upperParts).2).1
  have birthGround := ((M.mem_groundRelations _ _ _).1 historyBound).1
  change ZFSet.IsFunc (natSetCode (k + 1)) E0 births at birthFunction
  obtain ⟨e, he, lookup, _⟩ := birthHistory_scheduled_lookup k birthFunction
  have gridEntry : ZFSet.pair (natSetCode k)
      (ZFSet.pair (natSetCode (Nat.unpair k).1) (natSetCode (Nat.unpair k).2)) ∈ grid :=
    (natPresentation.pair_mem_graph (natPresentation.product natPresentation)
      omegaGridEquiv ⟨k⟩ (omegaGridEquiv ⟨k⟩)).2 rfl
  have chooseNext : ∃ q ∈ Q, ∃ event ∈ insert ∅ (ZFSet.prod stages U),
      ((e = ∅ ∧ q = p ∧ event = ∅) ∨
        (∃ alpha ∈ stages, ∃ y ∈ U, (∃ payload, y = ZFSet.pair q payload) ∧
          ZFSet.pair (natSetCode (Nat.unpair k).2) alpha ∈ e ∧
          ZFSet.pair (ZFSet.pair alpha p) y ∈ prepSelector ∧ event = ZFSet.pair alpha y)) := by
    rcases enumerationCases e he with idle | active
    · exact ⟨p, hp, ∅, ZFSet.mem_insert _ _, Or.inl ⟨idle, rfl, rfl⟩⟩
    · obtain ⟨alpha, level, _⟩ := active.2 _ (natSetCode_mem_omega (Nat.unpair k).2)
      have hAlpha := (ZFSet.pair_mem_prod.1 (active.1 level)).2
      obtain ⟨y, selected, _⟩ := prepared.2 _ (ZFSet.pair_mem_prod.2 ⟨hAlpha, hp⟩)
      have hy := (ZFSet.pair_mem_prod.1 (prepared.1 selected)).2
      obtain ⟨q, hq, payload, equal⟩ := outputs y hy
      exact ⟨q, hq, ZFSet.pair alpha y,
        ZFSet.mem_insert_of_mem _ (ZFSet.pair_mem_prod.2 ⟨hAlpha, hy⟩),
        Or.inr ⟨alpha, hAlpha, y, hy, ⟨payload, equal⟩, level, selected, rfl⟩⟩
  obtain ⟨q, hq, event, hEvent, branch⟩ := chooseNext
  obtain ⟨newE, selected, _⟩ := enumerated.2 q hq
  have hNewE := (ZFSet.pair_mem_prod.1 (enumerated.1 selected)).2
  let nextBirths := insert (ZFSet.pair (natSetCode (k + 1)) newE) births
  have nextFunction := finiteBirthHistory_extend (k + 1) birthFunction hNewE
  have nextGround := M.finiteBirthHistory_extend_mem pairing unions separation infinite
    (k + 1) birthGround (M.transitive hE0 hNewE)
  have nextBound := M.finiteHistory_bound (k + 1 + 1) nextGround nextFunction.1
  let next := ZFSet.pair (natSetCode (k + 1)) (ZFSet.pair q (ZFSet.pair nextBirths event))
  have nextMember : next ∈ M.fairPreparationStates Q stages U E0 enumSelector := by
    apply (M.mem_fairPreparationStates _ _ _ _ _ _).2
    refine ⟨ZFSet.pair_mem_prod.2 ⟨natSetCode_mem_omega _,
      ZFSet.pair_mem_prod.2 ⟨hq, ZFSet.pair_mem_prod.2 ⟨nextBound, hEvent⟩⟩⟩, ?_⟩
    exact ⟨natSetCode (k + 1), q, nextBirths, event, rfl, natSetCode_mem_omega _,
      ZFSet.omega_succ (natSetCode_mem_omega _), nextFunction.1,
      newE, hNewE, selected, (nextFunction.2.2.2 newE).2 rfl⟩
  refine ⟨next, nextMember, (M.pair_mem_fairPreparationTransition _ _ _ _ _ _ _ _ _).2
    ⟨member, nextMember, ?_⟩⟩
  exact ⟨natSetCode k, p, births, last, natSetCode (k + 1), q, nextBirths, event,
    rfl, rfl, rfl, natSetCode (Nat.unpair k).1, natSetCode_mem_omega _,
    natSetCode (Nat.unpair k).2, natSetCode_mem_omega _, e, he, newE, hNewE,
    gridEntry, lookup, selected, rfl, branch⟩





theorem exists_groundFairPreparationOrbit
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {Q stages U E0 enumSelector prepSelector p : ZFSet.{u}}
    (hQ : Q ∈ M.sets) (hStages : stages ∈ M.sets) (hU : U ∈ M.sets)
    (hE0 : E0 ∈ M.sets) (hEnum : enumSelector ∈ M.sets) (hPrep : prepSelector ∈ M.sets)
    (enumerated : ZFSet.IsFunc Q E0 enumSelector)
    (enumerationCases : ∀ e ∈ E0, e = ∅ ∨ ZFSet.IsFunc ZFSet.omega stages e)
    (prepared : ZFSet.IsFunc (ZFSet.prod stages Q) U prepSelector)
    (outputs : ∀ y ∈ U, ∃ q ∈ Q, ∃ payload, y = ZFSet.pair q payload)
    (member : p ∈ Q) :
    let grid := natPresentation.graph (natPresentation.product natPresentation) omegaGridEquiv
    let states := M.fairPreparationStates Q stages U E0 enumSelector
    let transition := M.fairPreparationTransition Q stages U E0 enumSelector prepSelector grid
    states ∈ M.sets ∧ transition ∈ M.sets ∧
      ∃ e ∈ E0, ZFSet.pair p e ∈ enumSelector ∧ ∃ orbit ∈ M.sets,
        ZFSet.IsFunc ZFSet.omega states orbit ∧
        (∀ state, ZFSet.pair ∅ state ∈ orbit ↔
          state = ZFSet.pair ∅ (ZFSet.pair p (ZFSet.pair {ZFSet.pair ∅ e} ∅))) ∧
        ∀ n ∈ ZFSet.omega, ∀ state next,
          ZFSet.pair n state ∈ orbit → ZFSet.pair (insert n n) next ∈ orbit →
          ZFSet.pair state next ∈ transition ∧
            FairPreparationStepCode ZFSet.omega E0 stages U enumSelector prepSelector grid state next := by
  dsimp only
  have omega := M.omega_mem separation infinite
  have gridGround := M.omega_grid_equiv_graph_mem pairing unions powers separation infinite
  have statesGround := M.fairPreparationStates_mem pairing unions powers separation
    hQ hStages hU hE0 hEnum omega
  have transitionGround := M.fairPreparationTransition_mem pairing unions powers separation
    hQ hStages hU hE0 hEnum hPrep gridGround omega
  obtain ⟨e, he, selected, initial⟩ :=
    M.exists_fairPreparation_initial pairing stages U hE0 enumerated member
  have serial := M.fairPreparationTransition_serial pairing unions separation infinite
    hE0 enumerated enumerationCases prepared outputs
  obtain ⟨orbit, ground, function, start, steps⟩ :=
    M.exists_groundSerialOrbit pairing unions powers separation infinite choice
      statesGround transitionGround initial serial
  refine ⟨statesGround, transitionGround, e, he, selected, orbit, ground, function, start, ?_⟩
  intro n hn state next first second
  have edge := steps n hn state next first second
  exact ⟨edge, ((M.pair_mem_fairPreparationTransition _ _ _ _ _ _ _ _ _).1 edge).2.2⟩

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundStoredVisitCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
universe u
variable (M : TransitiveGround.{u})

theorem varyingPreparationRelation_of_stored
    (stages packed Q upperOrder nodes T alpha p y meet : ZFSet.{u})
    (fields : Fin 15 → ZFSet.{u}) (hAlpha : alpha ∈ stages)
    (stored : ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed)
    (terms : fields 6 = T) (nodeCarrier : fields 10 = nodes)
    (meetCode : MeetOrderCode (fields 10) (fields 11) meet)
    (entry : ZFSet.pair p y ∈ M.storedPreparationRelation Q upperOrder nodes T
      (refinementDataHistoryLevels stages packed T) alpha meet fields) :
    ZFSet.pair (ZFSet.pair alpha p) y ∈
      M.varyingPreparationRelation stages packed Q upperOrder nodes T := by
  obtain ⟨hp, hy, code⟩ := (M.pair_mem_storedPreparationRelation Q upperOrder nodes T
    (refinementDataHistoryLevels stages packed T) alpha meet fields p y).1 entry
  have equal := meetCode.eq_canonicalMeetGraph
  exact (M.pair_mem_varyingPreparationRelation stages packed Q upperOrder nodes T alpha p y).2
    ⟨hAlpha, hp, hy, fields, stored, terms, nodeCarrier, equal ▸ meetCode, equal ▸ code⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticPreparedWitnessSelections
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
variable (hAlpha : alpha ∈ M.sets) (cutOrdinal : ordinalSetProperty alpha) (subset : alpha ⊆ stages)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "Q" => M.refinementHistoryForcing c.carrier T stages packed
local notation "LQ" => M.refinementHistoryForcing c.carrier T alpha (graphRestriction alpha packed)
local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t)
  t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 ordinal trace
local notation "lowerAct" => M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset
include hs hh ordinal trace hAlpha cutOrdinal subset
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

include infinite choice
theorem semanticStructuralPreparationWitness_bounds :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
    Q ∈ M.sets ∧ M.preparationWitnessBound b.carrier T Q ∈ M.sets ∧
      LQ ⊆ Q ∧ M.niceSupportNameCodes lowerAct (SetMembers.presentation LQ) T d.principalFix ⊆
        M.groundRelations T Q := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
  have hQ := M.refinementHistoryForcing_mem pairing unions powers separation carrier hT hs hPacked omega
  have inside : LQ ⊆ Q := by
    intro x hx
    have included := SetMembers.raw_mem (inc (SetMembers.ofMem x hx))
    rw [(run).inclusionFunction_raw ordinal cutOrdinal subset pairing unions powers separation
      infinite choice hs hPacked hT hAlpha carrier rowTop topMem topRows mono] at included
    simpa only [SetMembers.raw_ofMem] using included
  exact ⟨hQ, M.preparationWitnessBound_mem pairing unions powers separation nodes hT hQ omega,
    inside, M.niceSupportNameCodes_subset_groundRelations lowerAct (SetMembers.presentation LQ)
      T d.principalFix inside⟩

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

variable {stages history alpha : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
variable (ordinal : ordinalSetProperty stages)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
variable (hAlpha : alpha ∈ M.sets) (cutOrdinal : ordinalSetProperty alpha) (subset : alpha ⊆ stages)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "Q" => M.refinementHistoryForcing c.carrier T stages packed
local notation "LQ" => M.refinementHistoryForcing c.carrier T alpha (graphRestriction alpha packed)
local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t)
  t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 ordinal trace
local notation "lowerAct" => M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset
include hs hh ordinal trace hAlpha cutOrdinal subset
variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)

include infinite choice
theorem semanticStructuralPreparationWitness_mem :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha (graphRestriction alpha packed)
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation LQ
    let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    let indices := M.niceRefinementIndices lowerAct lower b d alpha T T2 valid
    ∀ A r k enumerations : ZFSet.{u},
    let selected := assignmentOnIndices indices T A
    let graphs := M.niceAssignmentClassGraphs lowerAct lower b d alpha T T2 valid selected
    let localBound := M.groundRelations T lower.carrier
    let J := relationImage selected localBound (graphs 0) ∪ relationImage selected localBound (graphs 1);
      r ∈ Q → k ∈ M.sets → enumerations ∈ M.sets →
      ZFSet.IsFunc J (M.supportedEqualityCertificateBound b.carrier
        (M.niceSupportNameCodes lowerAct lower T d.principalFix)) k →
      ZFSet.IsFunc J (M.synchronizedEnumerationBound b.carrier
        (M.niceSupportNameCodes lowerAct lower T d.principalFix)) enumerations →
      ZFSet.pair r (ZFSet.pair k enumerations) ∈ M.preparationWitnessBound b.carrier T Q := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha (graphRestriction alpha packed)
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation LQ
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  let indices := M.niceRefinementIndices lowerAct lower b d alpha T T2 valid
  dsimp only
  intro A r k enumerations hr hk he certificates enumerated
  have bounds := M.semanticStructuralPreparationWitness_bounds c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace hAlpha cutOrdinal subset infinite choice
  apply M.nicePreparationWitness_mem lowerAct lower T d.principalFix bounds.2.2.1
    (fun _ member => ?_) hr hk he certificates enumerated
  rcases ZFSet.mem_union.1 member with first | second
  · exact (mem_relationImage _ _ _ _).1 first |>.1
  · exact (mem_relationImage _ _ _ _).1 second |>.1

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundPreparedAlignedReferenceCollisions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.SynchronizedEnumerationCode
universe u

theorem codomain_mono {omega N N' B f e names : ZFSet.{u}}
    (code : SynchronizedEnumerationCode omega N B f e names) (subset : N ⊆ N') :
    SynchronizedEnumerationCode omega N' B f e names := by
  have widen {A graph : ZFSet.{u}} (function : ZFSet.IsFunc A N graph) :
      ZFSet.IsFunc A N' graph := by
    refine ⟨?_, function.2⟩
    intro z member
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (function.1 member)
    exact ZFSet.pair_mem_prod.2 ⟨hx, subset hy⟩
  exact ⟨widen code.1, code.2.1, widen code.2.2.1, code.2.2.2⟩

end PartitionPilot.Forcing.SynchronizedEnumerationCode



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u}
variable [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation I)
variable (T : ZFSet.{u}) (K : I → Subgroup G)

theorem preparedCertificateCode_of_selected
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (hT : T ∈ M.sets) (validT : ∀ tau ∈ T, IsName s tau)
    (graphGround : M.niceVisibilityGraph a s b T K ∈ M.sets)
    (nodeOrder meet J : ZFSet.{u}) (validJ : ∀ tau ∈ J, IsName s tau)
    (H : ConditionFilter P) (z : (M.nameDomain s).names)
    (F B f e names : ZFSet.{u}) (p : P)
    (selected : ZFSet.pair z.val.val (ZFSet.pair F (ZFSet.pair B f)) ∈
      M.supportedCertificateFamilyRelation a s b T K nodeOrder J validJ H)
    (filter : MeetFilterCode b.carrier nodeOrder meet F) (nonempty : B.Nonempty)
    (profile : M.DecidesVisibilityProfile a s b K T F z.val p)
    (equalities : ∀ v ∈ B, ∀ tau : Name s,
      tau.val ∈ M.niceSupportNameCodes a s T K → ZFSet.pair v tau.val ∈ f →
        Name.ForcesEq p z.val tau)
    (enumerated : SynchronizedEnumerationCode ZFSet.omega
      (M.niceSupportNameCodes a s T K) B f e names) :
    PreparedCertificateCode M s.carrier s.conditionOrder (s.encode p) b.carrier nodeOrder meet
      (M.groundRelations T s.carrier) (M.niceVisibilityGraph a s b T K) (s.encode ⊤)
      ZFSet.omega z.val.val F B f e names := by
  obtain ⟨_, _, _, _, _, nodes, basis, coinitial, function, supported⟩ :=
    M.supportedCertificateFamily_groundData a s b T K nodeOrder J validJ H
      z.val.val F B f selected
  have inside : M.niceSupportNameCodes a s T K ⊆ M.groundRelations T s.carrier := by
    intro tau member
    obtain ⟨ground, i, code⟩ := (M.mem_niceSupportNameCodes a s T K tau).1 member
    exact M.niceNameCandidates_subset a s T (K i)
      ((M.mem_niceNameCandidates a s T (K i) tau).2 ⟨ground, code⟩)
  have range : f ⊆ ZFSet.prod b.carrier (M.groundRelations T s.carrier) := by
    intro entry member
    obtain ⟨v, hv, tau, htau, rfl⟩ := ZFSet.mem_prod.1 (function.1 member)
    exact ZFSet.pair_mem_prod.2 ⟨nodes (basis hv), inside htau⟩
  have valid : ∀ tau ∈ M.groundRelations T s.carrier, IsName s tau := by
    intro tau member
    exact Name.isName_of_subset validT ((M.mem_groundRelations T s.carrier tau).1 member).2
  refine ⟨filter, ⟨basis, coinitial⟩, nonempty, enumerated.codomain_mono inside, ?_, ?_⟩
  · intro v tau entry
    have bounded := ZFSet.pair_mem_prod.1 (function.1 entry)
    rw [M.visibilitySupportIncidence_eq_niceSupportRelation a s b T K]
    exact supported v bounded.1 tau bounded.2 entry
  · apply (M.preparationForcingCode_iff a s b K pairing unions powers separation collection
      carrier order T (M.groundRelations T s.carrier) graphGround
      (M.groundRelations_mem pairing unions powers separation hT carrier) valid z F f range p).2
    refine ⟨profile, ?_⟩
    intro v tau _ entry
    have bounded := ZFSet.pair_mem_prod.1 (function.1 entry)
    exact equalities v bounded.1 tau bounded.2 entry





end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

namespace PreparedCertificateFamilyCode

theorem bounds_mono {M : TransitiveGround.{u}}
    {P order q nodes nodeOrder meet N visibility top omega J C E C' E' k enumerations : ZFSet.{u}}
    (code : PreparedCertificateFamilyCode M P order q nodes nodeOrder meet N visibility top omega J C E k enumerations)
    (certificates : C ⊆ C') (enumerationBound : E ⊆ E') :
    PreparedCertificateFamilyCode M P order q nodes nodeOrder meet N visibility top omega J C' E' k enumerations := by
  have widen {A B B' f : ZFSet.{u}} (function : ZFSet.IsFunc A B f) (inside : B ⊆ B') :
      ZFSet.IsFunc A B' f := by
    refine ⟨?_, function.2⟩
    intro entry member
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (function.1 member)
    exact ZFSet.pair_mem_prod.2 ⟨hx, inside hy⟩
  exact ⟨widen code.1 certificates, widen code.2.1 enumerationBound, code.2.2⟩

end PreparedCertificateFamilyCode
namespace TransitiveGround
variable (M : TransitiveGround.{u}) {I G P : Type u}
variable [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation I)
variable (T : ZFSet.{u}) (K : I → Subgroup G)

theorem preparedCertificateFamilyCode_of_selected
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (hT : T ∈ M.sets) (validT : ∀ tau ∈ T, IsName s tau)
    (graphGround : M.niceVisibilityGraph a s b T K ∈ M.sets)
    (nodeOrder meet J : ZFSet.{u}) (hJ : J ∈ M.sets) (validJ : ∀ tau ∈ J, IsName s tau)
    (H : ConditionFilter P) (p : P) (k enumerations : ZFSet.{u})
    (function : ZFSet.IsFunc J (M.supportedEqualityCertificateBound b.carrier
      (M.niceSupportNameCodes a s T K)) k)
    (selected : k ⊆ M.supportedCertificateFamilyRelation a s b T K nodeOrder J validJ H)
    (enumerated : ZFSet.IsFunc J (M.synchronizedEnumerationBound b.carrier
      (M.niceSupportNameCodes a s T K)) enumerations)
    (synchronized : ∀ j F B f e names,
      ZFSet.pair j (ZFSet.pair F (ZFSet.pair B f)) ∈ k →
      ZFSet.pair j (ZFSet.pair e names) ∈ enumerations →
      SynchronizedEnumerationCode ZFSet.omega (M.niceSupportNameCodes a s T K) B f e names)
    (certificates : ∀ (z : (M.nameDomain s).names) F B f,
      ZFSet.pair z.val.val (ZFSet.pair F (ZFSet.pair B f)) ∈ k →
      MeetFilterCode b.carrier nodeOrder meet F ∧ B.Nonempty ∧
      M.DecidesVisibilityProfile a s b K T F z.val p ∧
      (∀ v ∈ B, ∀ tau : Name s, tau.val ∈ M.niceSupportNameCodes a s T K →
        ZFSet.pair v tau.val ∈ f → Name.ForcesEq p z.val tau)) :
    PreparedCertificateFamilyCode M s.carrier s.conditionOrder (s.encode p) b.carrier nodeOrder meet
      (M.groundRelations T s.carrier) (M.niceVisibilityGraph a s b T K) (s.encode ⊤) ZFSet.omega J
      (M.supportedEqualityCertificateBound b.carrier (M.niceSupportNameCodes a s T K))
      (M.synchronizedEnumerationBound b.carrier (M.niceSupportNameCodes a s T K)) k enumerations := by
  refine ⟨function, enumerated, ?_⟩
  intro j F B f e names stored enumEntry
  have hj := (ZFSet.pair_mem_prod.1 (function.1 stored)).1
  let z : (M.nameDomain s).names := ⟨⟨j, validJ j hj⟩, M.transitive hJ hj⟩
  obtain ⟨filter, nonempty, profile, equalities⟩ := certificates z F B f stored
  exact M.preparedCertificateCode_of_selected a s b T K pairing unions powers separation collection
    carrier order hT validT graphGround nodeOrder meet J validJ H z F B f e names p
    (selected stored) filter nonempty profile equalities (synchronized j F B f e names stored enumEntry)

end TransitiveGround
end PartitionPilot.Forcing




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundStructuralBirthLevelSelectors
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

theorem structuralForcingTrace_birthLevelEnumerations
    (rows rowOrder rowTop rowAction G nodes nodeOrder nodeAction basis T T2 : ZFSet.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {stages history : ZFSet.{u}} (hRows : rows ∈ M.sets) (hG : G ∈ M.sets)
    (hNodes : nodes ∈ M.sets) (hOrder : nodeOrder ∈ M.sets) (hBasis : basis ∈ M.sets)
    (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (ordinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage rows rowOrder rowTop rowAction G nodes nodeOrder nodeAction
        basis T T2 level prior) stages history) :
    let packed := M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history
    let Q := M.refinementHistoryForcing rows T stages packed
    let levels := refinementDataHistoryLevels stages packed T
    Q ∈ M.sets ∧ M.groundRelations ZFSet.omega stages ∈ M.sets ∧
      M.birthLevelEnumerationRelation Q stages levels ∈ M.sets ∧
      ∃ selector ∈ M.sets, ZFSet.IsFunc Q (M.groundRelations ZFSet.omega stages) selector ∧
        selector ⊆ M.birthLevelEnumerationRelation Q stages levels ∧
        ∀ row A e, ZFSet.pair (ZFSet.pair row A) e ∈ selector →
          BirthLevelEnumerationCode ZFSet.omega stages A levels e := by
  have packed := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![G, nodes, nodeOrder, basis, T, T2, stages, history]
    (Fin.cases hG (Fin.cases hNodes (Fin.cases hOrder (Fin.cases hBasis
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun i => Fin.elim0 i)))))))))
  have run := M.structuralForcingTrace_recursiveOrder rows rowOrder rowTop rowAction
    G nodes nodeOrder nodeAction basis T T2 ordinal trace
  have omega := M.omega_mem separation infinite
  exact ⟨M.refinementHistoryForcing_mem pairing unions powers separation hRows hT hs packed omega,
    M.groundRelations_mem pairing unions powers separation omega hs,
    M.exists_refinementBirthLevelEnumerations pairing unions powers separation infinite choice
      hRows hT hs packed run.carriers.data⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMainFinalFairPreparationOrbits
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

theorem exists_preparationTransition
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
    ∀ (stages history alpha : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
      (ordinal : ordinalSetProperty stages)
      (trace : OrdinalRecursionTrace (fun level prior stage => stage =
        M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
          t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
          (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
      (member : alpha ∈ stages),
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
  let valid := M.refinementHistoryRowNameFamily_valid c (historyRun.carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  let lowerAct := M.semanticStructuralPrefixAction c a t b d ⊥ directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrder rowAction
        geometry.actors_ground geometry.carrier_ground nodeOrder nodeAction nodeMaps supports
        hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hh trace hAlpha cutOrdinal subset
  let inputs := M.semanticStructuralPrefix_preparation_inputs c a t b d ⊥ directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrder rowAction
        geometry.actors_ground geometry.carrier_ground nodeOrder nodeAction nodeMaps supports
        hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hs hh ordinal trace member
      infinite choice rowClosed
  let lowerGround := inputs.1
  let maps := inputs.2.2.1
  let indices := M.niceRefinementIndices lowerAct lower b d alpha T T2 valid
  let upperQ := M.refinementHistoryForcing c.carrier T stages packed
  letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let restriction := historyRun.restriction ordinal cutOrdinal subset c.conditionOrder_code
    ∀ (pUpper : SetMembers upperQ) (row A : ZFSet.{u})
      (_code : SetMembers.raw pUpper = ZFSet.pair row A),
  let selected := assignmentOnIndices indices T A
  let graphs := M.niceAssignmentClassGraphs lowerAct lower b d alpha T T2 valid selected
  let bound := M.groundRelations T lower.carrier
  let J := relationImage selected bound (graphs 0) ∪ relationImage selected bound (graphs 1)
    ∀ (_descent : ∀ H : ConditionFilter (SetMembers Q),
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
          Name.eval {p | H.mem p} τ.val = Name.eval {p | H.mem p} x.val),
      ∃ H : ConditionFilter (SetMembers Q),
        H.GenericFor (M.codedFamily lower) ∧
        H.GenericFor (formulaFamily (M.nameDomain lower)) ∧ H.mem (restriction pUpper) ∧
      ∃ (validJ : ∀ z ∈ J, IsName lower z) (hJ : J ∈ M.sets),
        M.groundEmbeddable J ZFSet.omega ∧
        (∀ z : Name lower, z.val ∈ J →
          HereditarilySymmetric lowerAct lower (d.principalSupportFamily ⊥ directed) z ∧
          Name.eval {q | H.mem q} z ⊆ Name.eval {q | H.mem q} (Name.familySet ⊤ T valid)) ∧
      ∃ (k : ZFSet.{u}) (hk : k ∈ M.sets),
        ZFSet.IsFunc J (M.supportedEqualityCertificateBound b.carrier
          (M.niceSupportNameCodes lowerAct lower T d.principalFix)) k ∧
        (∀ j F B f, ZFSet.pair j (ZFSet.pair F (ZFSet.pair B f)) ∈ k →
          j ∈ J ∧ F ∈ M.sets ∧ B ∈ M.sets ∧ f ∈ M.sets ∧
          M.groundEmbeddable B ZFSet.omega ∧ F ⊆ b.carrier ∧ B ⊆ F ∧
          (∀ v ∈ F, ∃ w ∈ B, ZFSet.pair w v ∈ geometry.order) ∧
          ZFSet.IsFunc B (M.niceSupportNameCodes lowerAct lower T d.principalFix) f ∧
          ∀ v ∈ B, ∀ tau ∈ M.niceSupportNameCodes lowerAct lower T d.principalFix,
            ZFSet.pair v tau ∈ f →
              ZFSet.pair v tau ∈ M.niceSupportRelation lowerAct lower b T d.principalFix) ∧
        k ⊆ M.supportedCertificateFamilyRelation lowerAct lower b T d.principalFix
          geometry.order J validJ H ∧
        ∃ q, H.mem q ∧ q ≤ restriction pUpper ∧
          Forces (M.nameDomain lower) supportedCertificateFamilyFormula
            (M.supportedCertificateFamilyEnv lowerAct lower t b T d.principalFix pairing unions powers
              separation collection lowerGround geometry.actors_ground geometry.carrier_ground
              (geometry.decoded_supportBasis_ground pairing unions powers separation)
              maps hT valid (M.omega_mem separation infinite) geometry.order J k
              geometry.order_ground hJ hk validJ) q ∧
          ∃ (r : SetMembers upperQ) (newRow newA : ZFSet.{u}),
            r ≤ pUpper ∧ restriction r = q ∧
            SetMembers.raw r = ZFSet.pair newRow newA ∧
            ZFSet.pair newRow row ∈ c.conditionOrder ∧ A ⊆ newA ∧
            SetMembers.raw (restriction r) = ZFSet.pair newRow
              (assignmentCut (refinementDataHistoryLevels stages packed T) alpha newA) ∧
            H.mem (restriction r) ∧
          Forces (M.nameDomain lower) supportedCertificateFamilyFormula
            (M.supportedCertificateFamilyEnv lowerAct lower t b T d.principalFix pairing unions powers
              separation collection lowerGround geometry.actors_ground geometry.carrier_ground
              (geometry.decoded_supportBasis_ground pairing unions powers separation)
              maps hT valid (M.omega_mem separation infinite) geometry.order J k
              geometry.order_ground hJ hk validJ) (restriction r) ∧
          ∃ enumerations ∈ M.sets,
            ZFSet.IsFunc J (M.synchronizedEnumerationBound b.carrier
              (M.niceSupportNameCodes lowerAct lower T d.principalFix)) enumerations ∧
            enumerations ⊆ M.certificateEnumerationRelation J b.carrier
              (M.niceSupportNameCodes lowerAct lower T d.principalFix) k ∧
            (∀ j F B f e names,
              ZFSet.pair j (ZFSet.pair F (ZFSet.pair B f)) ∈ k →
              ZFSet.pair j (ZFSet.pair e names) ∈ enumerations →
              SynchronizedEnumerationCode ZFSet.omega
                (M.niceSupportNameCodes lowerAct lower T d.principalFix) B f e names) ∧
            ∀ (z : (M.nameDomain lower).names) (F B f : ZFSet.{u}),
              ZFSet.pair z.val.val (ZFSet.pair F (ZFSet.pair B f)) ∈ k →
              F = M.visibleSupportProfile lowerAct lower b d T H (Name.eval {p | H.mem p} z.val) ∧
              MeetFilterCode geometry.carrier geometry.order geometry.meetGraph F ∧
              B.Nonempty ∧ M.DecidesVisibilityProfile lowerAct lower b d.principalFix T F z.val (restriction r) ∧
              (∀ v ∈ B, ∀ tau : Name lower, tau.val ∈ M.niceSupportNameCodes lowerAct lower T d.principalFix →
                ZFSet.pair v tau.val ∈ f → Name.ForcesEq (restriction r) z.val tau) ∧
              ∃ e ∈ M.sets, ∃ names ∈ M.sets,
                ZFSet.IsFunc ZFSet.omega B e ∧
                ZFSet.IsFunc ZFSet.omega (M.niceSupportNameCodes lowerAct lower T d.principalFix) names ∧
                (∀ v ∈ B, ∃ n ∈ ZFSet.omega, ZFSet.pair n v ∈ e) ∧
                (∀ n ∈ ZFSet.omega, ∀ v tau, ZFSet.pair n v ∈ e →
                  ZFSet.pair n tau ∈ names → ZFSet.pair v tau ∈ f) ∧
                (∀ n ∈ ZFSet.omega, ∀ v tau, ZFSet.pair n v ∈ e →
                  ZFSet.pair v tau ∈ f → ZFSet.pair n tau ∈ names) := by
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
  intro stages history alpha hs hh ordinal trace member
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
  let instLowerHistoryOrder := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let instLowerHistoryTop := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c (historyRun.carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  let lowerAct := M.semanticStructuralPrefixAction c a t b d ⊥ directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrder rowAction
        geometry.actors_ground geometry.carrier_ground nodeOrder nodeAction nodeMaps supports
        hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hh trace hAlpha cutOrdinal subset
  let inputs := M.semanticStructuralPrefix_preparation_inputs c a t b d ⊥ directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrder rowAction
        geometry.actors_ground geometry.carrier_ground nodeOrder nodeAction nodeMaps supports
        hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hs hh ordinal trace member
      infinite choice rowClosed
  let lowerGround := inputs.1
  let maps := inputs.2.2.1
  let indices := M.niceRefinementIndices lowerAct lower b d alpha T T2 valid
  let upperQ := M.refinementHistoryForcing c.carrier T stages packed
  let instUpperHistoryOrder := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let restriction := historyRun.restriction ordinal cutOrdinal subset c.conditionOrder_code
  let projection := M.semanticStructuralTrace_completeProjection c a t b d ⊥ directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrder rowAction geometry.actors_ground
    geometry.carrier_ground nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2
    closed1 closed2 children1 children2 topMem topRows hs hh ordinal trace alpha hAlpha cutOrdinal subset
    infinite choice
  intro pUpper row A code descent
  obtain ⟨H, hp, genericCoded, genericFormula⟩ :=
    M.exists_coded_ordinary_generic lower small lowerGround (restriction pUpper)
  let selected := assignmentOnIndices indices T A
  let graphs := M.niceAssignmentClassGraphs lowerAct lower b d alpha T T2 valid selected
  let bound := M.groundRelations T lower.carrier
  let J := relationImage selected bound (graphs 0) ∪ relationImage selected bound (graphs 1)
  have condition : ZFSet.pair row A ∈ upperQ := code ▸ SetMembers.raw_mem pUpper
  obtain ⟨validJ, hJ, smallJ, facts, k, hk, function, selectedCertificates,
      q, hq, qp, forced, enumerations, hEnumerations, enumerationFunction,
      enumerationRelation, synchronized, entries⟩ :=
    fulfilled.exists_prefixPreparationBatch c collection infinite choice small smallD irreflexive rowClosed
      a T T2 rowTop carrier rowOrder rowAction hT hT2 valid1 valid2 closed1 closed2 children1 children2
      topMem topRows stages history alpha hs hh ordinal trace member row A condition
      H genericCoded genericFormula (descent H genericCoded genericFormula) (restriction pUpper) hp
  obtain ⟨r, rp, rq⟩ := projection.lift pUpper q qp
  obtain ⟨newRow, _, newA, _, rCode⟩ := ZFSet.mem_prod.1
    (M.refinementHistoryForcing_shape c.carrier T stages packed (SetMembers.raw_mem r))
  have belowRaw : ZFSet.pair (SetMembers.raw r) (SetMembers.raw pUpper) ∈
      M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed := rp
  rw [rCode, code] at belowRaw
  have fields := (M.pair_mem_refinementHistoryOrder c.carrier c.conditionOrder T stages packed
    newRow newA row A).1 belowRaw
  have cut := historyRun.restrictionFunction_raw ordinal cutOrdinal subset r newRow newA rCode
  refine ⟨H, genericCoded, genericFormula, hp, validJ, hJ, smallJ, facts, k, hk, function, ?_,
    selectedCertificates, q, hq, qp, forced, r, newRow, newA, rp, rq, rCode,
    fields.2.2.1, fields.2.2.2, cut, rq.symm ▸ hq, rq.symm ▸ forced,
    enumerations, hEnumerations, enumerationFunction, enumerationRelation, synchronized, ?_⟩
  · intro j F B f entry
    exact M.supportedCertificateFamily_groundData lowerAct lower b T d.principalFix
      geometry.order J validJ H j F B f (selectedCertificates entry)
  · intro z F B f stored
    exact rq.symm ▸ entries z F B f stored






theorem exists_groundPreparationSteps
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
    ∀ (stages history alpha : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
      (ordinal : ordinalSetProperty stages)
      (trace : OrdinalRecursionTrace (fun level prior stage => stage =
        M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
          t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
          (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
      (member : alpha ∈ stages),
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
  let valid := M.refinementHistoryRowNameFamily_valid c (historyRun.carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  let lowerAct := M.semanticStructuralPrefixAction c a t b d ⊥ directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrder rowAction
        geometry.actors_ground geometry.carrier_ground nodeOrder nodeAction nodeMaps supports
        hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hh trace hAlpha cutOrdinal subset
  let upperQ := M.refinementHistoryForcing c.carrier T stages packed
  letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let fields := M.refinementLevelFormulaData lowerAct lower b d alpha T T2 valid
  let levels := refinementDataHistoryLevels stages packed T
  let relation := M.storedPreparationRelation upperQ
    (M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed)
    b.carrier T levels alpha geometry.meetGraph fields
    ∀ (_descent : ∀ H : ConditionFilter (SetMembers Q),
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
          Name.eval {p | H.mem p} τ.val = Name.eval {p | H.mem p} x.val),
      relation ∈ M.sets ∧ ∃ step ∈ M.sets,
        ZFSet.IsFunc upperQ (M.preparationWitnessBound b.carrier T upperQ) step ∧
        step ⊆ relation := by
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
  intro stages history alpha hs hh ordinal trace member
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
  let instLowerHistoryOrder := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let instLowerHistoryTop := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c (historyRun.carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  let lowerAct := M.semanticStructuralPrefixAction c a t b d ⊥ directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrder rowAction
        geometry.actors_ground geometry.carrier_ground nodeOrder nodeAction nodeMaps supports
        hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hh trace hAlpha cutOrdinal subset
  let inputs := M.semanticStructuralPrefix_preparation_inputs c a t b d ⊥ directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrder rowAction
        geometry.actors_ground geometry.carrier_ground nodeOrder nodeAction nodeMaps supports
        hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hs hh ordinal trace member
      infinite choice rowClosed
  let lowerGround := inputs.1
  let lowerOrder := inputs.2.1
  let upperQ := M.refinementHistoryForcing c.carrier T stages packed
  let instUpperHistoryOrder := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let restriction := historyRun.restriction ordinal cutOrdinal subset c.conditionOrder_code
  intro descent
  let fields := M.refinementLevelFormulaData lowerAct lower b d alpha T T2 valid
  let levels := refinementDataHistoryLevels stages packed T
  let upperOrder := M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed
  let relation := M.storedPreparationRelation upperQ upperOrder b.carrier T levels alpha geometry.meetGraph fields
  have packedGround := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases geometry.actors_ground (Fin.cases geometry.carrier_ground (Fin.cases nodeOrder
      (Fin.cases supports (Fin.cases hT (Fin.cases hT2
        (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have stored := M.semanticStructuralPrefix_refinementData_entry c a t b d ⊥ directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrder rowAction geometry.actors_ground
    geometry.carrier_ground nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2
    closed1 closed2 children1 children2 topMem topRows hs hh ordinal trace member
  have fieldGround : ∀ j, fields j ∈ M.sets :=
    M.refinementFormulaDataCode_fields_mem fields (M.pair_right (M.transitive packedGround stored))
  have bounds := M.semanticStructuralPreparationWitness_bounds c a t b d ⊥ directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrder rowAction geometry.actors_ground
    geometry.carrier_ground nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2
    closed1 closed2 children1 children2 topMem topRows hs hh ordinal trace hAlpha cutOrdinal subset
    infinite choice
  have upperOrderGround := M.refinementHistoryOrder_mem pairing unions powers separation
    carrier rowOrder hT hs packedGround omega
  have levelsGround := M.refinementDataHistoryLevels_mem pairing unions powers separation hs packedGround hT
  have meetCode : MeetOrderCode (fields 10) (fields 11) geometry.meetGraph := by
    change MeetOrderCode b.carrier b.conditionOrder geometry.meetGraph
    rw [geometry.decoded_order_eq]
    exact geometry.meet
  have relationGround : relation ∈ M.sets := M.storedPreparationRelation_mem
    pairing unions powers separation bounds.1 upperOrderGround geometry.carrier_ground hT
    levelsGround hAlpha geometry.meet_ground omega fields fieldGround meetCode
  have total : ∀ input ∈ upperQ, ∃ output ∈ M.preparationWitnessBound b.carrier T upperQ,
      ZFSet.pair input output ∈ relation := by
    intro input hInput
    obtain ⟨row, _, A, _, rfl⟩ := ZFSet.mem_prod.1
      (M.refinementHistoryForcing_shape c.carrier T stages packed hInput)
    let pUpper := SetMembers.ofMem (ZFSet.pair row A) hInput
    have pCode : SetMembers.raw pUpper = ZFSet.pair row A := SetMembers.raw_ofMem _ _
    let indices := M.niceRefinementIndices lowerAct lower b d alpha T T2 valid
    let selected := assignmentOnIndices indices T A
    let graphs := M.niceAssignmentClassGraphs lowerAct lower b d alpha T T2 valid selected
    let bound := M.groundRelations T lower.carrier
    let J := relationImage selected bound (graphs 0) ∪ relationImage selected bound (graphs 1)
    obtain ⟨H, _genericCoded, _genericFormula, _hp, validJ, hJ, _smallJ, _facts,
        k, hk, function, _groundData, selectedCertificates, q, _hq, _qp, _forced,
        r, newRow, newA, rp, _rq, rCode, _rowBelow, _retained, cut, _hr, _forcedr,
        enumerations, hEnumerations, enumerationFunction, _enumerationRelation, synchronized, entries⟩ :=
      fulfilled.exists_preparationTransition c collection infinite choice small smallD irreflexive rowClosed
        a T T2 rowTop carrier rowOrder rowAction hT hT2 valid1 valid2 closed1 closed2 children1 children2
        topMem topRows stages history alpha hs hh ordinal trace member pUpper row A pCode descent
    have prepared := M.preparedCertificateFamilyCode_of_selected lowerAct lower b T d.principalFix
      pairing unions powers separation collection lowerGround lowerOrder hT valid (fieldGround 13)
      geometry.order geometry.meetGraph J hJ validJ H (restriction r) k enumerations
      function selectedCertificates enumerationFunction synchronized (by
        intro z F B f entry
        have data := entries z F B f entry
        exact ⟨data.2.1, data.2.2.1, data.2.2.2.1, data.2.2.2.2.1⟩)
    have enlarged := prepared.bounds_mono
      (M.supportedEqualityCertificateBound_mono bounds.2.2.2)
      (M.synchronizedEnumerationBound_mono bounds.2.2.2)
    have witnessBound := M.semanticStructuralPreparationWitness_mem c a t b d ⊥ directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrder rowAction geometry.actors_ground
      geometry.carrier_ground nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2
      closed1 closed2 children1 children2 topMem topRows hs hh ordinal trace hAlpha cutOrdinal subset
      infinite choice A (SetMembers.raw r) k enumerations (SetMembers.raw_mem r) hk hEnumerations
      function enumerationFunction
    refine ⟨ZFSet.pair (SetMembers.raw r) (ZFSet.pair k enumerations), witnessBound, ?_⟩
    apply (M.pair_mem_storedPreparationRelation upperQ upperOrder b.carrier T levels alpha
      geometry.meetGraph fields _ _).2
    refine ⟨hInput, witnessBound, row, A, SetMembers.raw r, k, enumerations,
      SetMembers.raw (restriction r), rfl, rfl, ?_, ?_, ?_⟩
    · change ZFSet.pair (SetMembers.raw r) (SetMembers.raw pUpper) ∈ upperOrder at rp
      exact pCode ▸ rp
    · change ZFSet.pair (SetMembers.raw r) (SetMembers.raw (restriction r)) ∈
        rowAssignmentCutGraph upperQ Q levels alpha
      rw [rCode]
      exact (pair_mem_rowAssignmentCutGraph upperQ Q levels alpha newRow newA _).2
        ⟨rCode ▸ SetMembers.raw_mem r, SetMembers.raw_mem (restriction r), cut⟩
    · change PreparedCertificateFamilyCode M lower.carrier lower.conditionOrder
        (lower.encode (restriction r)) b.carrier b.conditionOrder geometry.meetGraph
        (M.groundRelations T lower.carrier) (M.niceVisibilityGraph lowerAct lower b T d.principalFix)
        (lower.encode ⊤) ZFSet.omega J
        (M.supportedEqualityCertificateBound b.carrier (M.groundRelations T upperQ))
        (M.synchronizedEnumerationBound b.carrier (M.groundRelations T upperQ)) k enumerations
      let codeAtOrder := fun orderCode : ZFSet.{u} =>
        PreparedCertificateFamilyCode M lower.carrier lower.conditionOrder
          (lower.encode (restriction r)) b.carrier orderCode geometry.meetGraph
          (M.groundRelations T lower.carrier) (M.niceVisibilityGraph lowerAct lower b T d.principalFix)
          (lower.encode ⊤) ZFSet.omega J
          (M.supportedEqualityCertificateBound b.carrier (M.groundRelations T upperQ))
          (M.synchronizedEnumerationBound b.carrier (M.groundRelations T upperQ)) k enumerations
      exact Eq.mpr (congrArg codeAtOrder geometry.decoded_order_eq) enlarged
  obtain ⟨step, ground, function, selected⟩ := M.uniformize_relation pairing unions powers separation choice
    bounds.1 bounds.2.1 relationGround total
  exact ⟨relationGround, step, ground, function, selected⟩






theorem exists_varyingGroundPreparationSteps
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
  let upperOrder := M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed
  let relation := M.varyingPreparationRelation stages packed upperQ upperOrder b.carrier T
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
      relation ∈ M.sets ∧ ∃ step ∈ M.sets,
        ZFSet.IsFunc (ZFSet.prod stages upperQ) (M.preparationWitnessBound b.carrier T upperQ) step ∧
        step ⊆ relation := by
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
  intro descent
  have packedGround := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases geometry.actors_ground (Fin.cases geometry.carrier_ground (Fin.cases nodeOrder
      (Fin.cases supports (Fin.cases hT (Fin.cases hT2
        (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have upperGround := M.refinementHistoryForcing_mem pairing unions powers separation
    carrier hT hs packedGround omega
  have upperOrderGround := M.refinementHistoryOrder_mem pairing unions powers separation
    carrier rowOrder hT hs packedGround omega
  have boundGround := M.preparationWitnessBound_mem pairing unions powers separation
    geometry.carrier_ground hT upperGround omega
  have inputGround := M.prod_mem pairing unions powers separation hs upperGround
  have relationGround : relation ∈ M.sets := M.varyingPreparationRelation_mem
    pairing unions powers separation hs packedGround upperGround upperOrderGround
    geometry.carrier_ground hT omega
  have total : ∀ input ∈ ZFSet.prod stages upperQ,
      ∃ output ∈ M.preparationWitnessBound b.carrier T upperQ,
        ZFSet.pair input output ∈ relation := by
    intro input hInput
    obtain ⟨alpha, member, p, hp, rfl⟩ := ZFSet.mem_prod.1 hInput
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
    let instLowerHistoryOrder := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    let instLowerHistoryTop := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation Q
    let valid := M.refinementHistoryRowNameFamily_valid c (historyRun.carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    let lowerAct := M.semanticStructuralPrefixAction c a t b d ⊥ directed T T2 rowTop
          pairing unions powers separation collection carrier rowOrder rowAction
          geometry.actors_ground geometry.carrier_ground nodeOrder nodeAction nodeMaps supports
          hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hh trace hAlpha cutOrdinal subset
    let fields := M.refinementLevelFormulaData lowerAct lower b d alpha T T2 valid
    obtain ⟨_fixedGround, fixedStep, _stepGround, function, selected⟩ :=
      fulfilled.exists_groundPreparationSteps c collection infinite choice small smallD irreflexive rowClosed
        a T T2 rowTop carrier rowOrder rowAction hT hT2 valid1 valid2 closed1 closed2 children1 children2
        topMem topRows stages history alpha hs hh ordinal trace member (descent alpha member)
    obtain ⟨y, entry, _unique⟩ := function.2 p hp
    have hy := (ZFSet.pair_mem_prod.1 (function.1 entry)).2
    have stored := M.semanticStructuralPrefix_refinementData_entry c a t b d ⊥ directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrder rowAction geometry.actors_ground
      geometry.carrier_ground nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2
      closed1 closed2 children1 children2 topMem topRows hs hh ordinal trace member
    have meetCode : MeetOrderCode (fields 10) (fields 11) geometry.meetGraph := by
      change MeetOrderCode b.carrier b.conditionOrder geometry.meetGraph
      rw [geometry.decoded_order_eq]
      exact geometry.meet
    exact ⟨y, hy, M.varyingPreparationRelation_of_stored stages packed upperQ upperOrder b.carrier T
      alpha p y geometry.meetGraph fields member stored rfl rfl meetCode (selected entry)⟩
  obtain ⟨step, ground, function, selected⟩ := M.uniformize_relation pairing unions powers separation
    choice inputGround boundGround relationGround total
  exact ⟨relationGround, step, ground, function, selected⟩






theorem exists_groundFairPreparationOrbit_oai
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
  let upperOrder := M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed
  let relation := M.varyingPreparationRelation stages packed upperQ upperOrder b.carrier T
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
    ∀ p ∈ upperQ,
      ∃ enumSelector ∈ M.sets,
        ZFSet.IsFunc upperQ (M.groundRelations ZFSet.omega stages) enumSelector ∧
        enumSelector ⊆ M.birthLevelEnumerationRelation upperQ stages
          (refinementDataHistoryLevels stages packed T) ∧
      ∃ E0 ∈ M.sets, ZFSet.IsFunc upperQ E0 enumSelector ∧
      ∃ prepSelector ∈ M.sets,
        ZFSet.IsFunc (ZFSet.prod stages upperQ)
          (M.preparationWitnessBound b.carrier T upperQ) prepSelector ∧
        prepSelector ⊆ relation ∧
      ∃ e ∈ E0, ZFSet.pair p e ∈ enumSelector ∧ ∃ orbit ∈ M.sets,
        ZFSet.IsFunc ZFSet.omega
          (M.fairPreparationStates upperQ stages (M.preparationWitnessBound b.carrier T upperQ)
            E0 enumSelector) orbit ∧
        (∀ state, ZFSet.pair ∅ state ∈ orbit ↔
          state = ZFSet.pair ∅ (ZFSet.pair p (ZFSet.pair {ZFSet.pair ∅ e} ∅))) ∧
        ∀ n ∈ ZFSet.omega, ∀ state next,
          ZFSet.pair n state ∈ orbit → ZFSet.pair (insert n n) next ∈ orbit →
          FairPreparationStepCode ZFSet.omega E0 stages (M.preparationWitnessBound b.carrier T upperQ)
            enumSelector prepSelector
            (natPresentation.graph (natPresentation.product natPresentation) omegaGridEquiv)
            state next := by
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
  obtain ⟨_relationGround, prepSelector, hPrep, prepFunction, prepSelected⟩ :=
    fulfilled.exists_varyingGroundPreparationSteps c collection infinite choice small smallD
      irreflexive rowClosed a T T2 rowTop carrier rowOrder rowAction hT hT2 valid1 valid2
      closed1 closed2 children1 children2 topMem topRows stages history hs hh ordinal trace descent
  obtain ⟨hQ, _enumBoundGround, _birthRelationGround, enumSelector, hEnum,
      enumFunction, enumSelected, _birthCodes⟩ :=
    M.structuralForcingTrace_birthLevelEnumerations c.carrier c.conditionOrder rowTop
      (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 pairing unions powers separation collection
      infinite choice carrier geometry.actors_ground geometry.carrier_ground nodeOrder supports
      hT hT2 hs hh ordinal trace
  let E0 := relationImage upperQ (M.groundRelations ZFSet.omega stages) enumSelector
  obtain ⟨hE0, _rangeBound, enumCases, _rangeEntries⟩ :=
    M.birthEnumerationRange_spec pairing unions powers separation hQ hs omega
      hEnum enumFunction enumSelected
  have rangeFunction : ZFSet.IsFunc upperQ E0 enumSelector := by
    refine ⟨?_, enumFunction.2⟩
    intro z member
    obtain ⟨q, hq, e, he, rfl⟩ := ZFSet.mem_prod.1 (enumFunction.1 member)
    exact ZFSet.pair_mem_prod.2 ⟨hq, (mem_relationImage _ _ _ e).2 ⟨he, q, hq, member⟩⟩
  have hU := M.preparationWitnessBound_mem pairing unions powers separation
    geometry.carrier_ground hT hQ omega
  have outputShape : ∀ y ∈ M.preparationWitnessBound b.carrier T upperQ,
      ∃ q ∈ upperQ, ∃ payload, y = ZFSet.pair q payload := by
    intro y hy
    obtain ⟨q, hq, payload, _, equal⟩ := ZFSet.mem_prod.1 hy
    exact ⟨q, hq, payload, equal⟩
  obtain ⟨_statesGround, _transitionGround, e, he, chosen, orbit, hOrbit,
      orbitFunction, initial, steps⟩ :=
    M.exists_groundFairPreparationOrbit pairing unions powers separation infinite choice
      hQ hs hU hE0 hEnum hPrep rangeFunction enumCases prepFunction outputShape hp
  refine ⟨enumSelector, hEnum, enumFunction, enumSelected, E0, hE0, rangeFunction,
    prepSelector, hPrep, prepFunction, prepSelected, e, he, chosen,
    orbit, hOrbit, orbitFunction, initial, ?_⟩
  intro n hn state next first second
  exact (steps n hn state next first second).2

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
end

theorem solution.{u, v} : type_of% @OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.exists_groundFairPreparationOrbit_oai.{u, v} := @OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.exists_groundFairPreparationOrbit_oai.{u, v}
