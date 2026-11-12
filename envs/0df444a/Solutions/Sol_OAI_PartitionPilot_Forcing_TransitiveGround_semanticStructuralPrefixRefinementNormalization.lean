-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefixRefinementNormalization
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:31:43.662987+00:00
-- url     : https://prove2.me/submissions/fac6b491-bfd3-460a-8526-d159392e38e2

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
import Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_semanticStructuralPrefixRefinementEnvironment
import Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_semanticStructuralPrefixSharedCondition_spec

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_OrbitPairGraphNames
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall _root_.OAI.PartitionPilot.Forcing.Name.boundedNames_small _root_.OAI.PartitionPilot.Forcing.Name.unionIndices_small _root_.OAI.PartitionPilot.Forcing.PosetAction.mixIndices_small
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing

open SetRealization Compression.RecursiveMaps
universe u v w
variable {G : Type v} [Group G] {P : Type u} [PartialOrder P]

namespace HereditarilySymmetric
variable {a : PosetAction G P} {s : Presentation P} {F : NormalSubgroupFamily G}

theorem assemble {α : Type w} [Small.{u} α] (names : α → Name s) (conditions : α → P)
    (sym : F.mem (a.stabilizer s (Name.assemble names conditions)))
    (children : ∀ i, HereditarilySymmetric a s F (names i)) :
    HereditarilySymmetric a s F (Name.assemble names conditions) := by
  refine HereditarilySymmetric.mk sym ?_
  intro σ p entry
  obtain ⟨i, rfl, _⟩ := (Name.entry_assemble names conditions σ p).1 entry
  exact children i

theorem assemble_common [OrderTop P] {α : Type w} [Small.{u} α]
    (names : α → Name s) (children : ∀ i, HereditarilySymmetric a s F (names i))
    (K : Subgroup G) (hK : F.mem K) (fixed : ∀ g ∈ K, ∀ i, a.act s g (names i) = names i) :
    HereditarilySymmetric a s F (Name.assemble names (fun _ => ⊤)) := by
  apply assemble names (fun _ => ⊤) _ children
  apply F.upward hK
  intro g hg
  change Name.rename s (a.iso g) (Name.assemble names (fun _ => ⊤)) = _
  rw [Name.rename_assemble]
  have top : a.iso g ⊤ = ⊤ := (a.iso g).map_top
  simp only [top]
  apply congrArg (fun ns : α → Name s => Name.assemble ns (fun _ => ⊤))
  funext i
  exact fixed g hg i

theorem singleton [OrderTop P] {τ : Name s} (h : HereditarilySymmetric a s F τ) :
    HereditarilySymmetric a s F (Name.singleton ⊤ τ) :=
  assemble_common (fun _ : Unit => τ) (fun _ => h) (a.stabilizer s τ) h.symmetric
    (fun _ fixed _ => fixed)

theorem unorderedPair [OrderTop P] {σ τ : Name s}
    (hσ : HereditarilySymmetric a s F σ) (hτ : HereditarilySymmetric a s F τ) :
    HereditarilySymmetric a s F (Name.unorderedPair ⊤ σ τ) := by
  apply assemble_common (fun b : Bool => if b then σ else τ)
    (fun b => by cases b; exact hτ; exact hσ)
    (a.stabilizer s σ ⊓ a.stabilizer s τ) (F.inf hσ.symmetric hτ.symmetric)
  intro g fixed b
  cases b
  · exact fixed.2
  · exact fixed.1

theorem orderedPair [OrderTop P] {σ τ : Name s}
    (hσ : HereditarilySymmetric a s F σ) (hτ : HereditarilySymmetric a s F τ) :
    HereditarilySymmetric a s F (Name.orderedPair ⊤ σ τ) :=
  hσ.singleton.unorderedPair (hσ.unorderedPair hτ)

end HereditarilySymmetric
end PartitionPilot.Forcing



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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_FinitePrincipalNameSupports
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.Name
open SetRealization
universe u
variable {Upper Lower : Type u} [PartialOrder Upper]
variable (s : Presentation Upper) (t : Presentation Lower)
variable (inclusion : Lower → Upper) (J : ZFSet.{u}) (tau : Name s)

theorem pair_mem_crossStageMembershipCode (sigma : Name t) (p : Lower) :
    ZFSet.pair sigma.val (t.encode p) ∈ crossStageMembershipCode s t inclusion J tau ↔
      sigma.val ∈ J ∧ ForcesMem (inclusion p) (rename s inclusion sigma) tau := by
  change (_ ∈ ZFSet.sep _ _) ↔ _
  rw [ZFSet.mem_sep]
  constructor
  · rintro ⟨bound, nu, q, equal, forced⟩
    obtain ⟨names, conditions⟩ := ZFSet.pair_inj.1 equal
    have sameName : sigma = nu := Subtype.ext names
    have sameCondition : p = q := t.injective conditions
    exact ⟨(ZFSet.pair_mem_prod.1 bound).1, sameName.symm ▸ sameCondition.symm ▸ forced⟩
  · rintro ⟨member, forced⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨member, t.encode_mem p⟩, sigma, p, rfl, forced⟩

theorem entry_crossStageMembershipName (valid : ∀ z ∈ J, IsName t z)
    (sigma : Name t) (p : Lower) :
    Entry sigma (crossStageMembershipName s t inclusion J valid tau) p ↔
      sigma.val ∈ J ∧ ForcesMem (inclusion p) (rename s inclusion sigma) tau :=
  pair_mem_crossStageMembershipCode s t inclusion J tau sigma p

end PartitionPilot.Forcing.Name



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundNiceNameNormalization
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.Name
open SetRealization
universe u
variable {P : Type u} [Preorder P] [OrderTop P] {s : Presentation P}

theorem eval_subset_familySet_of_code_subset (H : ConditionFilter P)
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (tau : Name s)
    (shape : tau.val ⊆ ZFSet.prod T s.carrier) :
    eval {p | H.mem p} tau ⊆ eval {p | H.mem p} (familySet ⊤ T valid) := by
  intro x member
  obtain ⟨sigma, p, entry, _, value⟩ := (mem_eval {p | H.mem p} tau x).1 member
  have term : sigma.val ∈ T := (ZFSet.pair_mem_prod.1 (shape entry)).1
  exact (mem_eval_familySet {p | H.mem p} ⊤ H.top_mem T valid x).2
    ⟨sigma, term, value⟩

end PartitionPilot.Forcing.Name



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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_PairFamilyEvaluation
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization Compression.RecursiveMaps
universe u v
variable {P : Type u} {s : Presentation P}

variable {G : Type v} [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (F : NormalSubgroupFamily G)

theorem orderedPairNameFamily_hs {X Y : ZFSet.{u}}
    (validX : ∀ z ∈ X, IsName s z) (validY : ∀ z ∈ Y, IsName s z)
    (childrenX : ∀ τ : Name s, τ.val ∈ X → HereditarilySymmetric a s F τ)
    (childrenY : ∀ τ : Name s, τ.val ∈ Y → HereditarilySymmetric a s F τ) :
    ∀ τ : Name s, τ.val ∈ orderedPairNameFamily (s.encode ⊤) X Y →
      HereditarilySymmetric a s F τ := by
  intro τ hτ
  obtain ⟨x, hx, y, hy, equal⟩ := (mem_orderedPairNameFamily _ X Y τ.val).1 hτ
  let σ : Name s := ⟨x, validX x hx⟩
  let ν : Name s := ⟨y, validY y hy⟩
  have same : τ = Name.orderedPair ⊤ σ ν :=
    Subtype.ext (equal.trans (Name.orderedPair_code ⊤ σ ν).symm)
  rw [same]
  exact (childrenX σ hx).orderedPair (childrenY ν hy)

theorem orderedPairNameFamily_closed {X Y : ZFSet.{u}}
    (validX : ∀ z ∈ X, IsName s z) (validY : ∀ z ∈ Y, IsName s z)
    (closedX : ∀ g (τ : Name s), τ.val ∈ X → (a.act s g τ).val ∈ X)
    (closedY : ∀ g (τ : Name s), τ.val ∈ Y → (a.act s g τ).val ∈ Y) :
    ∀ g (τ : Name s), τ.val ∈ orderedPairNameFamily (s.encode ⊤) X Y →
      (a.act s g τ).val ∈ orderedPairNameFamily (s.encode ⊤) X Y := by
  intro g τ hτ
  obtain ⟨x, hx, y, hy, equal⟩ := (mem_orderedPairNameFamily _ X Y τ.val).1 hτ
  let σ : Name s := ⟨x, validX x hx⟩
  let ν : Name s := ⟨y, validY y hy⟩
  have same : τ = Name.orderedPair ⊤ σ ν :=
    Subtype.ext (equal.trans (Name.orderedPair_code ⊤ σ ν).symm)
  have acted : a.act s g τ = Name.orderedPair ⊤ (a.act s g σ) (a.act s g ν) := by
    rw [same]
    change Name.rename s (a.iso g) _ = _
    rw [Name.rename_orderedPair, (a.iso g).map_top]
    rfl
  exact (mem_orderedPairNameFamily _ X Y _).2
    ⟨(a.act s g σ).val, closedX g σ hx, (a.act s g ν).val, closedY g ν hy,
      (congrArg Subtype.val acted).trans (Name.orderedPair_code ⊤ _ _)⟩

theorem iteratedPairNameFamily_hs {T : ZFSet.{u}}
    (valid : ∀ z ∈ T, IsName s z)
    (children : ∀ τ : Name s, τ.val ∈ T → HereditarilySymmetric a s F τ) (n : Nat) :
    ∀ τ : Name s, τ.val ∈ iteratedPairNameFamily (s.encode ⊤) T n →
      HereditarilySymmetric a s F τ := by
  induction n with
  | zero => exact children
  | succ n ih =>
    exact orderedPairNameFamily_hs a F
      (iteratedPairNameFamily_valid ⊤ valid n) valid ih children

theorem iteratedPairNameFamily_closed {T : ZFSet.{u}}
    (valid : ∀ z ∈ T, IsName s z)
    (closed : ∀ g (τ : Name s), τ.val ∈ T → (a.act s g τ).val ∈ T) (n : Nat) :
    ∀ g (τ : Name s), τ.val ∈ iteratedPairNameFamily (s.encode ⊤) T n →
      (a.act s g τ).val ∈ iteratedPairNameFamily (s.encode ⊤) T n := by
  induction n with
  | zero => exact closed
  | succ n ih =>
    exact orderedPairNameFamily_closed a
      (iteratedPairNameFamily_valid ⊤ valid n) valid ih closed

end PartitionPilot.Forcing



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_StructuralPreparationSourceImages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
universe u
variable (M : TransitiveGround.{u})
variable (G nodes nodeOrder nodeAction basis T T2 : ZFSet.{u})

theorem structuralAssignmentImage_domain_restrict {stages earlier history : ZFSet.{u}}
    (function : FunctionGraphOn stages history) (subset : earlier ⊆ stages) (g A : ZFSet.{u}) :
    M.structuralAssignmentImage G nodes nodeOrder nodeAction basis T T2 earlier history g A =
      M.structuralAssignmentImage G nodes nodeOrder nodeAction basis T T2 stages history g
        (ZFSet.sep (fun x => x ∈ M.structuralAssignments G nodes nodeOrder basis T T2 earlier history) A) := by
  apply ZFSet.ext
  intro y
  rw [M.structuralAssignmentImage_entry, M.structuralAssignmentImage_entry]
  constructor
  · rintro ⟨x, hx, edge⟩
    obtain ⟨whole, source⟩ :=
      (M.structuralAssignmentActionGraph_prefix_entry G nodes nodeOrder nodeAction basis T T2 function subset g x y).1 edge
    exact ⟨x, ZFSet.mem_sep.2 ⟨hx, source⟩, whole⟩
  · rintro ⟨x, hx, edge⟩
    obtain ⟨member, source⟩ := ZFSet.mem_sep.1 hx
    exact ⟨x, member,
      (M.structuralAssignmentActionGraph_prefix_entry G nodes nodeOrder nodeAction basis T T2 function subset g x y).2
        ⟨edge, source⟩⟩

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticStructuralDataSupport
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

variable {stages history : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
variable (ordinal : ordinalSetProperty stages)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "Q" => M.refinementHistoryForcing c.carrier T stages packed
open scoped ZFSet
local notation "rawGraph" => rawRowAssignmentActionGraph t.carrier Q c.carrier (⋃₀ ⋃₀ Q)
  (M.structuralAssignments t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history)
  (a.actionGraph c t)
  (M.structuralAssignmentActionGraph t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 stages history)
include hs hh ordinal trace

local notation "act" => M.semanticStructuralAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace

theorem semanticStructuralAction_graph :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    (act).actionGraph (SetMembers.presentation Q) t = rawGraph := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  unfold semanticStructuralAction
  exact PosetActionCode.toPresentedPosetAction_graph _ _ _

theorem semanticStructuralAction_coordinates :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    ∀ (g : G) (p : SetMembers Q) (r : R) (A : ZFSet.{u}),
      SetMembers.raw p = ZFSet.pair (c.encode r) A →
      SetMembers.raw ((act).iso g p) = ZFSet.pair (c.encode (a.iso g r))
        (M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
          (supportBasisCode b t d.principalFix) T T2 stages history (t.encode g) A) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  intro g p r A code
  have edge := ((act).triple_mem_actionGraph (SetMembers.presentation Q) t g p ((act).iso g p)).2 rfl
  rw [M.semanticStructuralAction_graph] at edge
  change ZFSet.pair (ZFSet.pair (t.encode g) (SetMembers.raw p)) (SetMembers.raw ((act).iso g p)) ∈ _ at edge
  obtain ⟨q, D, _, target⟩ := exists_presentedRowAssignmentCoordinates c
    (M.structuralForcingCarrier_shape c.carrier t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 stages history)
    (SetMembers.raw_mem ((act).iso g p))
  rw [code, target] at edge
  obtain ⟨_, _, row, data⟩ := (presentedRowAssignmentGraph_entry a c t Q _ _ g r q A D).1 edge
  rw [target, row, data]
  rfl

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticStructuralCutActions
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
local notation "upperAct" => M.semanticStructuralAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace
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

theorem semanticStructuralInclusion_equivariant :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
    ∀ (g : G) (p : SetMembers LQ), (upperAct).iso g (inc p) = inc ((lowerAct).iso g p) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
  intro g p
  obtain ⟨r, A, _, code⟩ := exists_presentedRowAssignmentCoordinates c
    (M.refinementHistoryForcing_shape c.carrier T alpha (graphRestriction alpha packed)) (SetMembers.raw_mem p)
  have includeCode := (run).inclusionFunction_raw ordinal cutOrdinal subset pairing unions powers separation
    infinite choice hs hPacked hT hAlpha carrier rowTop topMem topRows mono
  have member := code ▸ SetMembers.raw_mem p
  have data := ((M.pair_mem_stageOneCandidateBound _ _ _ _ _).1
    ((M.mem_refinementHistoryForcing c.carrier T alpha (graphRestriction alpha packed) _).1 member).1).2.2.1
  have fixedCut := (run).carriers.data.prefix_assignments_cut subset data
  have equalImage := M.structuralAssignmentImage_domain_restrict t.carrier b.carrier b.conditionOrder
    (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 trace.1 subset (t.encode g) A
  rw [← M.structuralAssignments_cut_eq t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 subset, fixedCut] at equalImage
  apply SetMembers.raw_injective Q
  rw [M.semanticStructuralAction_coordinates c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace g (inc p) r A
      ((includeCode p).trans code),
    includeCode ((lowerAct).iso g p),
    M.semanticStructuralPrefixAction_coordinates c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset g p r A code]
  exact congrArg (ZFSet.pair (c.encode (a.iso g r))) equalImage.symm

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

variable {stages history : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
variable (ordinal : ordinalSetProperty stages)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history

local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 ordinal trace
include hs hh ordinal trace

variable {alpha : ZFSet.{u}} (hAlpha : alpha ∈ M.sets)
variable (cutOrdinal : ordinalSetProperty alpha) (subset : alpha ⊆ stages)
local notation "LQ" => M.refinementHistoryForcing c.carrier T alpha (graphRestriction alpha packed)
local notation "lowerAct" => M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset
include hAlpha cutOrdinal subset

omit hs in
theorem semanticStructuralPrefixPower_family (n : Nat) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
    let X := iteratedPairNameFamily (ZFSet.pair rowTop ∅) T n
    ∃ _valid : ∀ z ∈ X, IsName (SetMembers.presentation LQ) z,
      X ∈ M.sets ∧
      (∀ g (tau : Name (SetMembers.presentation LQ)), tau.val ∈ X →
        ((lowerAct).act (SetMembers.presentation LQ) g tau).val ∈ X) ∧
      (∀ tau : Name (SetMembers.presentation LQ), tau.val ∈ X →
        HereditarilySymmetric lowerAct (SetMembers.presentation LQ)
          (d.principalSupportFamily base directed) tau) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha (graphRestriction alpha packed)
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let image := fun g A => M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder
    (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 alpha history (t.encode g) A
  have coordinates := M.semanticStructuralPrefixAction_coordinates c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset
  have emptyImage : ∀ g, image g ∅ = ∅ := fun g =>
    M.structuralAssignmentImage_empty t b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 alpha history (t.encode g)
  obtain ⟨valid, closed, symmetric⟩ := M.refinementHistoryRowNameFamily_transport c
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier a lowerAct image coordinates emptyImage
    (d.principalSupportFamily base directed) T valid1 closed1 symmetric1
  have topEq := M.refinementHistoryDecodedTop_eq c.conditionOrder_code T alpha (graphRestriction alpha packed)
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  have validPower := iteratedPairNameFamily_valid ⊤ valid n
  have closedPower := iteratedPairNameFamily_closed lowerAct valid closed n
  have symmetricPower := iteratedPairNameFamily_hs lowerAct
    (d.principalSupportFamily base directed) valid symmetric n
  rw [topEq] at validPower closedPower symmetricPower
  exact ⟨validPower, M.iteratedPairNameFamily_mem pairing unions powers separation
    (M.orderedPair_mem pairing (M.transitive carrier topMem) (M.empty_mem ⟨T, hT⟩)) hT n,
    closedPower, symmetricPower⟩

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_RefinementValidityReindex
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

theorem refinementValidity_empty (T : ZFSet.{u}) :
    RefinementValidityCode T ∅ ∅ ∅ := by
  have relation : EquivalenceRelationCode (∅ : ZFSet.{u}) ∅ :=
    ⟨by simp, by simp, by simp, by simp⟩
  exact ⟨by simp, relation, relation, fun _ h => h⟩

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundSharedConditionalNames
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
attribute [-simp] _root_.OAI.PartitionPilot.Forcing.GroundChronologicalMainTransition.comp_identity _root_.OAI.PartitionPilot.Forcing.GroundChronologicalMainTransition.identity_comp _root_.OAI.PartitionPilot.Forcing.GroundMainTransition.comp_identity _root_.OAI.PartitionPilot.Forcing.GroundMainTransition.identity_comp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
open SetRealization SetFormula
universe u

namespace SetFormula

theorem realize_sharedConditionFormula (U : Set ZFSet.{u}) {n : Nat}
    (phi : SetFormula n) (i : Fin n) (env : Fin n → ZFSet.{u}) (x : ZFSet.{u}) :
    Realize U (sharedConditionFormula phi i) (extend x env) ↔
      Realize U phi env ∧ x ∈ env i := by
  change (Realize U (reindex Fin.succ phi) (extend x env) ∧ x ∈ env i) ↔ _
  rw [realize_reindex]
  rfl

end SetFormula

end

namespace Name
open SetRealization SetFormula
universe u
variable {P : Type u} [Preorder P] [OrderTop P] {s : Presentation P}

theorem eval_sharedConditionName (D : NameDomain s) {n : Nat}
    (phi : SetFormula n) (env : Assignment D n) (i : Fin n)
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (family : familySet ⊤ T valid ∈ D.names) (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily D)) :
    eval {p | H.mem p} (sharedConditionName D phi env i T valid) =
      ZFSet.sep (fun x => Realize (D.values {p | H.mem p}) phi
        (evalAssignment {p | H.mem p} env) ∧ x ∈ eval {p | H.mem p} (env i).val)
        (eval {p | H.mem p} (familySet ⊤ T valid)) := by
  rw [sharedConditionName, eval_separationName D H generic
    (sharedConditionFormula phi i) env family]
  apply ZFSet.ext
  intro x
  simp only [ZFSet.mem_sep, realize_sharedConditionFormula]
  rfl

theorem eval_sharedConditionName_of_true (D : NameDomain s) {n : Nat}
    (phi : SetFormula n) (env : Assignment D n) (i : Fin n)
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (family : familySet ⊤ T valid ∈ D.names) (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily D))
    (truth : Realize (D.values {p | H.mem p}) phi
      (evalAssignment {p | H.mem p} env)) :
    eval {p | H.mem p} (sharedConditionName D phi env i T valid) =
      eval {p | H.mem p} (env i).val ∩ eval {p | H.mem p} (familySet ⊤ T valid) := by
  rw [eval_sharedConditionName D phi env i T valid family H generic]
  apply ZFSet.ext
  intro x
  simp only [ZFSet.mem_sep, ZFSet.mem_inter, truth, true_and]
  exact and_comm

theorem eval_sharedConditionName_of_subset (D : NameDomain s) {n : Nat}
    (phi : SetFormula n) (env : Assignment D n) (i : Fin n)
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (family : familySet ⊤ T valid ∈ D.names) (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily D))
    (truth : Realize (D.values {p | H.mem p}) phi
      (evalAssignment {p | H.mem p} env))
    (subset : eval {p | H.mem p} (env i).val ⊆
      eval {p | H.mem p} (familySet ⊤ T valid)) :
    eval {p | H.mem p} (sharedConditionName D phi env i T valid) =
      eval {p | H.mem p} (env i).val := by
  rw [eval_sharedConditionName_of_true D phi env i T valid family H generic truth]
  apply ZFSet.ext
  intro x
  exact ⟨fun member => (ZFSet.mem_inter.1 member).1,
    fun member => ZFSet.mem_inter.2 ⟨member, subset member⟩⟩

theorem eval_sharedConditionName_of_false (D : NameDomain s) {n : Nat}
    (phi : SetFormula n) (env : Assignment D n) (i : Fin n)
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (family : familySet ⊤ T valid ∈ D.names) (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily D))
    (falsehood : ¬ Realize (D.values {p | H.mem p}) phi
      (evalAssignment {p | H.mem p} env)) :
    eval {p | H.mem p} (sharedConditionName D phi env i T valid) = ∅ := by
  rw [eval_sharedConditionName D phi env i T valid family H generic]
  apply ZFSet.ext
  intro x
  simp [falsehood]

end Name

namespace Name
open SetRealization SetFormula
universe u
variable {P : Type u} [Preorder P] [OrderTop P] {s : Presentation P}

theorem eval_refinementConditionNames_coherent (D : NameDomain s)
    (env : Assignment D 4) (T : Fin 3 → ZFSet.{u})
    (valid : ∀ i, ∀ z ∈ T i, IsName s z)
    (family : ∀ i, familySet ⊤ (T i) (valid i) ∈ D.names)
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily D))
    (shape : ∀ i : Fin 3, (env i.castSucc).val.val ⊆ ZFSet.prod (T i) s.carrier) :
    (Realize (D.values {p | H.mem p}) BoundedFormula.refinementValidityFormula.toFormula
      (evalAssignment {p | H.mem p} env) ∧
      ∀ i : Fin 3, eval {p | H.mem p} (refinementConditionNames D env T valid i) =
        eval {p | H.mem p} (env i.castSucc).val) ∨
    (¬ Realize (D.values {p | H.mem p}) BoundedFormula.refinementValidityFormula.toFormula
      (evalAssignment {p | H.mem p} env) ∧
      ∀ i : Fin 3, eval {p | H.mem p} (refinementConditionNames D env T valid i) = ∅) := by
  classical
  by_cases truth : Realize (D.values {p | H.mem p})
      BoundedFormula.refinementValidityFormula.toFormula (evalAssignment {p | H.mem p} env)
  · refine Or.inl ⟨truth, ?_⟩
    intro i
    exact eval_sharedConditionName_of_subset D BoundedFormula.refinementValidityFormula.toFormula
      env i.castSucc (T i) (valid i) (family i) H generic truth
      (eval_subset_familySet_of_code_subset H (T i) (valid i) (env i.castSucc).val (shape i))
  · refine Or.inr ⟨truth, ?_⟩
    intro i
    exact eval_sharedConditionName_of_false D BoundedFormula.refinementValidityFormula.toFormula
      env i.castSucc (T i) (valid i) (family i) H generic truth

theorem eval_refinementConditionNames_valid (D : NameDomain s)
    (env : Assignment D 4) (T : Fin 3 → ZFSet.{u})
    (valid : ∀ i, ∀ z ∈ T i, IsName s z)
    (family : ∀ i, familySet ⊤ (T i) (valid i) ∈ D.names)
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily D))
    (shape : ∀ i : Fin 3, (env i.castSucc).val.val ⊆ ZFSet.prod (T i) s.carrier) :
    RefinementValidityCode (eval {p | H.mem p} (env 3).val)
      (eval {p | H.mem p} (refinementConditionNames D env T valid 0))
      (eval {p | H.mem p} (refinementConditionNames D env T valid 1))
      (eval {p | H.mem p} (refinementConditionNames D env T valid 2)) := by
  let evaluated : TransitiveGround.{u} :=
    ⟨D.values {p | H.mem p}, D.values_transitive {p | H.mem p}⟩
  rcases eval_refinementConditionNames_coherent D env T valid family H generic shape with
    ⟨truth, equal⟩ | ⟨_, equal⟩
  · rw [equal 0, equal 1, equal 2]
    exact (evaluated.realize_refinementValidityFormula
      (evalAssignment {p | H.mem p} env) (fun i => ⟨env i, rfl⟩)).1 truth
  · rw [equal 0, equal 1, equal 2]
    exact refinementValidity_empty _

theorem eval_refinementConditionNames_of_valid (D : NameDomain s)
    (env : Assignment D 4) (T : Fin 3 → ZFSet.{u})
    (valid : ∀ i, ∀ z ∈ T i, IsName s z)
    (family : ∀ i, familySet ⊤ (T i) (valid i) ∈ D.names)
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily D))
    (shape : ∀ i : Fin 3, (env i.castSucc).val.val ⊆ ZFSet.prod (T i) s.carrier)
    (oldValid : RefinementValidityCode (eval {p | H.mem p} (env 3).val)
      (eval {p | H.mem p} (env 0).val) (eval {p | H.mem p} (env 1).val)
      (eval {p | H.mem p} (env 2).val)) :
    ∀ i : Fin 3, eval {p | H.mem p} (refinementConditionNames D env T valid i) =
      eval {p | H.mem p} (env i.castSucc).val := by
  let evaluated : TransitiveGround.{u} :=
    ⟨D.values {p | H.mem p}, D.values_transitive {p | H.mem p}⟩
  have truth := (evaluated.realize_refinementValidityFormula
    (evalAssignment {p | H.mem p} env) (fun i => ⟨env i, rfl⟩)).2 oldValid
  intro i
  exact eval_sharedConditionName_of_subset D BoundedFormula.refinementValidityFormula.toFormula
    env i.castSucc (T i) (valid i) (family i) H generic truth
    (eval_subset_familySet_of_code_subset H (T i) (valid i) (env i.castSucc).val (shape i))

end Name

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundSharedRefinementValidity
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
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] [OrderTop P]
variable (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (J : Fin 3 → ZFSet.{u}) (hJ : ∀ i, J i ∈ M.sets)
variable (valid : ∀ i, ∀ z ∈ J i, IsName s z)
variable (env : Assignment (M.nameDomain s) 4)

theorem refinementConditionAssignment_entry (i : Fin 3) :
    ((M.refinementConditionAssignment s pairing unions powers separation collection
      carrier order J hJ valid env) i.castSucc).val =
      Name.refinementConditionNames (M.nameDomain s) env J valid i := by
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))) i

include pairing unions powers separation collection carrier order hJ in
theorem sharedRefinementValidity_top (small : M.sets.Countable)
    (shape : ∀ i : Fin 3, (env i.castSucc).val.val ⊆ ZFSet.prod (J i) s.carrier) :
    Forces (M.nameDomain s) BoundedFormula.refinementValidityFormula.toFormula
      (M.refinementConditionAssignment s pairing unions powers separation collection
        carrier order J hJ valid env) ⊤ := by
  apply (M.ordinaryForces_iff_all_generics s small carrier _ _ ⊤).2
  intro H _ generic
  let evaluated : TransitiveGround.{u} :=
    ⟨(M.nameDomain s).values {p | H.mem p},
      (M.nameDomain s).values_transitive {p | H.mem p}⟩
  let newEnv := M.refinementConditionAssignment s pairing unions powers separation collection
    carrier order J hJ valid env
  apply (evaluated.realize_refinementValidityFormula
    (evalAssignment {p | H.mem p} newEnv) (fun i => ⟨newEnv i, rfl⟩)).2
  have family : ∀ i, Name.familySet ⊤ (J i) (valid i) ∈ (M.nameDomain s).names :=
    fun i => M.familySet_mem s ⊤ pairing unions powers separation (hJ i)
      (M.transitive carrier (s.encode_mem ⊤)) (valid i)
  exact Name.eval_refinementConditionNames_valid (M.nameDomain s) env J valid
    family H generic shape

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_CrossStageMembershipNameActions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.Name
open SetRealization Compression.RecursiveMaps
universe u v
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]
variable {G : Type v} [Group G]
variable (upper : PosetAction G P) (lower : PosetAction G Q)
variable (s : Presentation P) (t : Presentation Q) (inclusion : Q → P)
variable (J : ZFSet.{u}) (valid : ∀ z ∈ J, IsName t z)
variable (equivariant : ∀ g p, inclusion (lower.iso g p) = upper.iso g (inclusion p))
variable (closed : ∀ g (sigma : Name t), sigma.val ∈ J → (lower.act t g sigma).val ∈ J)
include equivariant closed

theorem crossStageMembershipName_act (g : G) (tau : Name s) :
    lower.act t g (crossStageMembershipName s t inclusion J valid tau) =
      crossStageMembershipName s t inclusion J valid (upper.act s g tau) := by
  apply Name.ext
  intro sigma p
  obtain ⟨sigma, rfl⟩ := (lower.nameEquiv t g).surjective sigma
  obtain ⟨p, rfl⟩ := (lower.iso g).surjective p
  change Entry (lower.act t g sigma)
    (lower.act t g (crossStageMembershipName s t inclusion J valid tau)) (lower.iso g p) ↔
    Entry (lower.act t g sigma)
      (crossStageMembershipName s t inclusion J valid (upper.act s g tau)) (lower.iso g p)
  rw [lower.entry_act, entry_crossStageMembershipName, entry_crossStageMembershipName]
  have member : (lower.act t g sigma).val ∈ J ↔ sigma.val ∈ J := by
    constructor
    · intro h
      have back := closed g⁻¹ (lower.act t g sigma) h
      simpa only [lower.act_inv_left] using back
    · exact closed g sigma
  rw [member, equivariant,
    ← lower.act_rename_of_equivariant upper t s inclusion equivariant,
    upper.forcesMem_act_iff]

theorem crossStageMembershipName_stabilizer (tau : Name s) :
    upper.stabilizer s tau ≤
      lower.stabilizer t (crossStageMembershipName s t inclusion J valid tau) := by
  intro g fixed
  change upper.act s g tau = tau at fixed
  change lower.act t g (crossStageMembershipName s t inclusion J valid tau) = _
  rw [crossStageMembershipName_act upper lower s t inclusion J valid equivariant closed, fixed]

end PartitionPilot.Forcing.Name

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_CrossStageParameterSupports
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.Name
open SetRealization SetFormula
universe u v
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q] [OrderTop Q]
variable {G : Type v} [Group G]

theorem crossStageParameter_support
    (upper : PosetAction G P) (lower : PosetAction G Q)
    (s : Presentation P) (t : Presentation Q) (inclusion : Q → P)
    (equivariant : ∀ g p, inclusion (lower.iso g p) = upper.iso g (inclusion p))
    {n : Nat} (J : Fin n → ZFSet.{u})
    (valid : ∀ i z, z ∈ J i → IsName t z)
    (closed : ∀ i g (sigma : Name t), sigma.val ∈ J i → (lower.act t g sigma).val ∈ J i)
    (tau : Fin n → Name s) (D : NameDomain t) (env : Assignment D (n + 1))
    (names : ∀ i, (env i.castSucc).val = crossStageMembershipName s t inclusion (J i) (valid i) (tau i))
    (T : ZFSet.{u}) (validT : ∀ z ∈ T, IsName t z)
    (closedT : ∀ g (sigma : Name t), sigma.val ∈ T → (lower.act t g sigma).val ∈ T)
    (family : (env (Fin.last n)).val = familySet ⊤ T validT)
    (K : Subgroup G) (supported : ∀ i, K ≤ upper.stabilizer s (tau i)) :
    ∀ j, K ≤ lower.stabilizer t (env j).val := by
  intro j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · intro g _
    change lower.act t g (env (Fin.last n)).val = (env (Fin.last n)).val
    rw [family]
    exact act_familySet lower T validT closedT g
  · rw [names i]
    exact (supported i).trans
      (crossStageMembershipName_stabilizer upper lower s t inclusion (J i) (valid i)
        equivariant (closed i) (tau i))

end PartitionPilot.Forcing.Name

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticStructuralRefinementNormalization
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
variable (hAlpha : alpha ∈ M.sets) (cutOrdinal : ordinalSetProperty alpha) (subset : alpha ⊆ stages)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "Q" => M.refinementHistoryForcing c.carrier T stages packed
local notation "LQ" => M.refinementHistoryForcing c.carrier T alpha (graphRestriction alpha packed)
local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t)
  t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 ordinal trace
local notation "upperAct" => M.semanticStructuralAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace
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

local notation "termData" => M.structuralTrace_finitePowerTerms c c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 pairing unions powers separation
  carrier hT valid1 topMem ordinal trace

theorem semanticStructuralPrefixRefinementNormalization_oai
    (small : M.sets.Countable) (degrees : Fin 3 → Nat) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha (graphRestriction alpha packed)
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let upper := SetMembers.presentation Q
    let lower := SetMembers.presentation LQ
    let J := fun i => iteratedPairNameFamily (ZFSet.pair rowTop ∅) T (degrees i)
    let valid := fun i => (termData (degrees i)).2 alpha cutOrdinal subset
    let validT := (termData 0).2 alpha cutOrdinal subset
    ∀ tau : Fin 3 → (M.nameDomain upper).names,
      ∃ env : Assignment (M.nameDomain lower) 4,
        (∀ i : Fin 3, (env i.castSucc).val =
          Name.crossStageMembershipName upper lower inc (J i) (valid i) (tau i).val) ∧
        (env 3).val = Name.familySet ⊤ T validT ∧
      ∃ normalized : Assignment (M.nameDomain lower) 4,
        (∀ i : Fin 3, (normalized i.castSucc).val =
          Name.refinementConditionNames (M.nameDomain lower) env J valid i) ∧
        normalized 3 = env 3 ∧
        Forces (M.nameDomain lower) BoundedFormula.refinementValidityFormula.toFormula normalized ⊤ ∧
        (∀ C : Subgroup G, (d.principalSupportFamily base directed).mem C →
          (∀ i, C ≤ (upperAct).stabilizer upper (tau i).val) → ∀ i : Fin 3,
          NiceNameCode lowerAct lower (J i) C (normalized i.castSucc).val.val ∧
          HereditarilySymmetric lowerAct lower (d.principalSupportFamily base directed)
            (normalized i.castSucc).val) ∧
        ∀ H : ConditionFilter (SetMembers LQ),
          H.GenericFor (formulaFamily (M.nameDomain lower)) →
          RefinementValidityCode (Name.eval {p | H.mem p} (env 3).val)
            (Name.eval {p | H.mem p} (env 0).val) (Name.eval {p | H.mem p} (env 1).val)
            (Name.eval {p | H.mem p} (env 2).val) →
          ∀ i : Fin 3, Name.eval {p | H.mem p} (normalized i.castSucc).val =
            Name.eval {p | H.mem p} (env i.castSucc).val := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha (graphRestriction alpha packed)
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let upper := SetMembers.presentation Q
  let lower := SetMembers.presentation LQ
  let J := fun i => iteratedPairNameFamily (ZFSet.pair rowTop ∅) T (degrees i)
  let valid := fun i => (termData (degrees i)).2 alpha cutOrdinal subset
  let validT := (termData 0).2 alpha cutOrdinal subset
  dsimp only
  intro tau
  obtain ⟨env, names, last⟩ := M.semanticStructuralPrefixRefinementEnvironment
    c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround
    rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hs hh ordinal trace hAlpha cutOrdinal subset infinite choice degrees tau
  have hLower : lower.carrier ∈ M.sets :=
    M.refinementHistoryForcing_mem pairing unions powers separation carrier hT hAlpha
      (M.graphRestriction_mem unions separation hAlpha hPacked) omega
  have hOrder : lower.conditionOrder ∈ M.sets := by
    rw [M.refinementHistoryDecodedOrder_eq]
    exact M.refinementHistoryOrder_mem pairing unions powers separation carrier rowOrderGround hT hAlpha
      (M.graphRestriction_mem unions separation hAlpha hPacked) omega
  have hJ : ∀ i : Fin 3, J i ∈ M.sets := fun i => (termData (degrees i)).1
  have shape : ∀ i : Fin 3, (env i.castSucc).val.val ⊆ ZFSet.prod (J i) lower.carrier := by
    intro i
    rw [names i]
    exact Name.crossStageMembershipCode_subset upper lower inc (J i) (tau i).val
  let normalized := M.refinementConditionAssignment lower pairing unions powers separation collection
    hLower hOrder J hJ valid env
  have entry : ∀ i : Fin 3, (normalized i.castSucc).val =
      Name.refinementConditionNames (M.nameDomain lower) env J valid i :=
    fun i => M.refinementConditionAssignment_entry lower pairing unions powers separation collection
      hLower hOrder J hJ valid env i
  refine ⟨env, names, last, normalized, entry, rfl, ?_, ?_, ?_⟩
  · exact M.sharedRefinementValidity_top lower pairing unions powers separation collection
      hLower hOrder J hJ valid env small shape
  · intro C member supported
    have closed : ∀ i g (sigma : Name lower), sigma.val ∈ J i →
        ((lowerAct).act lower g sigma).val ∈ J i := by
      intro i
      obtain ⟨_, _, terms, _⟩ := M.semanticStructuralPrefixPower_family
        c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround
        rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
        symmetric1 symmetric2 topMem topRows hh ordinal trace hAlpha cutOrdinal subset (degrees i)
      exact terms
    have closedT : ∀ g (sigma : Name lower), sigma.val ∈ T →
        ((lowerAct).act lower g sigma).val ∈ T := by
      obtain ⟨_, _, terms, _⟩ := M.semanticStructuralPrefixPower_family
        c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround
        rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
        symmetric1 symmetric2 topMem topRows hh ordinal trace hAlpha cutOrdinal subset 0
      exact terms
    have fixed := Name.crossStageParameter_support upperAct lowerAct upper lower inc
      (fun g p => (M.semanticStructuralInclusion_equivariant c a t b d base directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
        nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
        topMem topRows hs hh ordinal trace hAlpha cutOrdinal subset infinite choice g p).symm)
      J valid closed (fun i => (tau i).val) (M.nameDomain lower) env names T validT closedT last C supported
    intro i
    obtain ⟨_, _, spec⟩ := M.semanticStructuralPrefixSharedCondition_spec
      c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround
      rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
      symmetric1 symmetric2 topMem topRows hs hh ordinal trace hAlpha cutOrdinal subset (degrees i)
    have nice := spec 4 BoundedFormula.refinementValidityFormula.toFormula env i.castSucc C member fixed
    rw [entry i]
    exact nice.2
  · intro H generic oldValid i
    rw [entry i]
    have family : ∀ j, Name.familySet ⊤ (J j) (valid j) ∈ (M.nameDomain lower).names :=
      fun j => M.familySet_mem lower ⊤ pairing unions powers separation (hJ j)
        (M.transitive hLower (lower.encode_mem ⊤)) (valid j)
    exact Name.eval_refinementConditionNames_of_valid (M.nameDomain lower) env J valid
      family H generic shape oldValid i

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

theorem solution.{u} : type_of% @OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefixRefinementNormalization_oai.{u} := @OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefixRefinementNormalization_oai.{u}
