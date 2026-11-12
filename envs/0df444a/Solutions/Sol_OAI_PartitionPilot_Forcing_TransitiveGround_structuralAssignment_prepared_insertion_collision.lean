-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.TransitiveGround.structuralAssignment_prepared_insertion_collision
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:14:19.263168+00:00
-- url     : https://prove2.me/submissions/ba2855ce-b3b7-4e05-a397-f05a77dce39b

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_StageOneDataBoundLaws
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
open SetRealization SetFormula
universe u

theorem mem_stageOneDataBounds (A I T S L mu X r anchors tuples z : ZFSet.{u}) :
    z ∈ stageOneDataBounds A I T S L mu X r anchors tuples ↔
      ∃ v ∈ A, ∃ D ∈ L, ∃ i ∈ I, ∃ u ∈ T, ∃ w ∈ T, ∃ E ∈ L,
        ∃ fu ∈ S, ∃ fw ∈ S, z = ZFSet.pair v D ∧ v = stageOneAssignment i u w ∧
          ZFSet.pair i E ∈ anchors ∧ ZFSet.pair E D ∈ r ∧
          ZFSet.pair fu u ∈ tuples ∧ ZFSet.pair fw w ∈ tuples ∧
          RowPositionBound mu X r fu D ∧ RowPositionBound mu X r fw D := by
  rw [stageOneDataBounds, ZFSet.mem_sep]
  constructor
  · exact And.right
  · rintro ⟨v,hv,D,hD,i,hi,u,hu,w,hw,E,hE,fu,hfu,fw,hfw,equal,rest⟩
    exact ⟨equal.symm ▸ ZFSet.pair_mem_prod.2 ⟨hv,hD⟩,
      v,hv,D,hD,i,hi,u,hu,w,hw,E,hE,fu,hfu,fw,hfw,equal,rest⟩

theorem pair_mem_stageOneDataBounds (A I T S L mu X r anchors tuples v D : ZFSet.{u}) :
    ZFSet.pair v D ∈ stageOneDataBounds A I T S L mu X r anchors tuples ↔
      v ∈ A ∧ D ∈ L ∧ ∃ i ∈ I, ∃ u ∈ T, ∃ w ∈ T, ∃ E ∈ L, ∃ fu ∈ S, ∃ fw ∈ S,
        v = stageOneAssignment i u w ∧ ZFSet.pair i E ∈ anchors ∧ ZFSet.pair E D ∈ r ∧
        ZFSet.pair fu u ∈ tuples ∧ ZFSet.pair fw w ∈ tuples ∧
        RowPositionBound mu X r fu D ∧ RowPositionBound mu X r fw D := by
  rw [mem_stageOneDataBounds]
  constructor
  · rintro ⟨v',hv,D',hD,i,hi,u,hu,w,hw,E,hE,fu,hfu,fw,hfw,equal,rest⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_injective equal
    exact ⟨hv,hD,i,hi,u,hu,w,hw,E,hE,fu,hfu,fw,hfw,rest⟩
  · rintro ⟨hv,hD,i,hi,u,hu,w,hw,E,hE,fu,hfu,fw,hfw,rest⟩
    exact ⟨v,hv,D,hD,i,hi,u,hu,w,hw,E,hE,fu,hfu,fw,hfw,rfl,rest⟩

end

open SetRealization
universe u

theorem stageOneDataBounds_assignment_entry (A I T S L mu X r anchors tuples i u w D : ZFSet.{u}) :
    ZFSet.pair (stageOneAssignment i u w) D ∈ stageOneDataBounds A I T S L mu X r anchors tuples ↔
      stageOneAssignment i u w ∈ A ∧ D ∈ L ∧ i ∈ I ∧ u ∈ T ∧ w ∈ T ∧
      ∃ E ∈ L, ∃ fu ∈ S, ∃ fw ∈ S,
        ZFSet.pair i E ∈ anchors ∧ ZFSet.pair E D ∈ r ∧
        ZFSet.pair fu u ∈ tuples ∧ ZFSet.pair fw w ∈ tuples ∧
        RowPositionBound mu X r fu D ∧ RowPositionBound mu X r fw D := by
  rw [pair_mem_stageOneDataBounds]
  constructor
  · rintro ⟨member,hD,i',hi,u',hu,w',hw,E,hE,fu,hfu,fw,hfw,equal,rest⟩
    obtain ⟨rfl,rfl,rfl⟩ := (stageOneAssignment_eq_iff i u w i' u' w').1 equal
    exact ⟨member,hD,hi,hu,hw,E,hE,fu,hfu,fw,hfw,rest⟩
  · rintro ⟨member,hD,hi,hu,hw,E,hE,fu,hfu,fw,hfw,rest⟩
    exact ⟨member,hD,i,hi,u,hu,w,hw,E,hE,fu,hfu,fw,hfw,rfl,rest⟩

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

variable {G : Type v} [Group G] (a : PosetAction G P)

theorem refinementClass_support (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (closed : ∀ g (z : Name s), z.val ∈ T → (a.act s g z).val ∈ T)
    (R w : Name s) (K : Subgroup G)
    (relation : K ≤ a.stabilizer s R) (representative : K ≤ a.stabilizer s w) :
    K ≤ a.stabilizer s (refinementClass T valid R w) := by
  intro g hg
  change a.act s g _ = _
  rw [act_refinementClass a T valid closed, relation hg, representative hg]

theorem refinementClass_hs (F : NormalSubgroupFamily G)
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (closed : ∀ g (z : Name s), z.val ∈ T → (a.act s g z).val ∈ T)
    (children : ∀ z : Name s, z.val ∈ T → HereditarilySymmetric a s F z)
    (R w : Name s) (K : Subgroup G) (member : F.mem K)
    (relation : K ≤ a.stabilizer s R) (representative : K ≤ a.stabilizer s w) :
    HereditarilySymmetric a s F (refinementClass T valid R w) :=
  HereditarilySymmetric.mk
    (F.upward member (refinementClass_support a T valid closed R w K relation representative))
    (fun z p entry => children z ((entry_refinementClass T valid R w z p).1 entry).1)

end PartitionPilot.Forcing.Name



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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundNiceRefinementClassSupports
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
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (level T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
variable (valid2 : ∀ z ∈ T2, IsName s z)
variable (indices : NiceRefinementIndexSystem M a s b d level T T2 valid valid2)

include indices in
theorem niceRefinementClasses_supported_by_block
    (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (closed : ∀ g (tau : Name s), tau.val ∈ T → (a.act s g tau).val ∈ T)
    (children : ∀ tau : Name s, tau.val ∈ T →
      HereditarilySymmetric a s (d.principalSupportFamily base directed) tau)
    (C E D : L) (U Rf Rc : (M.nameDomain s).names)
    (member : refinementIndexCode level (b.encode C) (b.encode E)
      U.val.val Rf.val.val Rc.val.val ∈ M.niceRefinementIndices a s b d level T T2 valid)
    (anchor : E ≤ D) (representatives : Fin 2 → Name s)
    (positions : ∀ i, d.principalFix D ≤ a.stabilizer s (representatives i)) :
    ∀ i, d.principalFix D ≤ a.stabilizer s
      (Name.refinementClass T valid (![Rc.val, Rf.val] i) (representatives i)) ∧
      HereditarilySymmetric a s (d.principalSupportFamily base directed)
        (Name.refinementClass T valid (![Rc.val, Rf.val] i) (representatives i)) := by
  obtain ⟨lower, _, fine, coarse, _⟩ := (indices.typed_entries C E U Rf Rc).1 member
  have atC := d.principalFix_antitone (le_trans (le_of_lt lower) anchor)
  have fineSupport := ((M.name_mem_niceNameCandidates a s T2 (d.principalFix C) Rf.val).1 fine).2.2
  have coarseSupport := ((M.name_mem_niceNameCandidates a s T2 (d.principalFix C) Rc.val).1 coarse).2.2
  have relation : ∀ i : Fin 2, d.principalFix D ≤ a.stabilizer s (![Rc.val, Rf.val] i) :=
    Fin.cases (atC.trans coarseSupport)
      (Fin.cases (atC.trans fineSupport) (fun j => Fin.elim0 j))
  intro i
  exact ⟨Name.refinementClass_support a T valid closed _ _ (d.principalFix D)
    (relation i) (positions i),
    Name.refinementClass_hs a (d.principalSupportFamily base directed) T valid closed children
      _ _ (d.principalFix D) ⟨D, le_rfl⟩ (relation i) (positions i)⟩

end PartitionPilot.Forcing.TransitiveGround

end

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

end TransitiveGround
end

open SetRealization SetFormula
universe u

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundPreparedCertificateActionPackages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

theorem visibilityProfileImage_entry {L G : Type u} [Group G] [PartialOrder L]
    (b : Presentation L) (d : PosetAction G L) (F : ZFSet.{u}) (g : G) (v : L) :
    b.encode (d.iso g v) ∈ relationImage F b.carrier (b.graph b (d.iso g)) ↔
      b.encode v ∈ F := by
  constructor
  · intro member
    obtain ⟨_, x, hx, edge⟩ := (mem_relationImage F b.carrier (b.graph b (d.iso g)) _).1 member
    obtain ⟨w, equal⟩ := (b.mem_graph b (d.iso g) _).1 edge
    have parts := ZFSet.pair_inj.1 equal
    have same : w = v := (d.iso g).injective (b.injective parts.2)
    subst w
    rw [parts.1]
    exact hx
  · intro member
    exact (mem_relationImage F b.carrier (b.graph b (d.iso g)) _).2
      ⟨b.encode_mem _, b.encode v, member, (b.pair_mem_graph b (d.iso g) v _).2 rfl⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u}) {L G P : Type u}
variable [Group G] [PartialOrder L] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
variable {T : ZFSet.{u}}
variable (closed : ∀ g (z : Name s), z.val ∈ T → (a.act s g z).val ∈ T)

include pairing unions powers separation collection carrier maps closed in
theorem decidesVisibilityProfile_act (F : ZFSet.{u}) (z : Name s) (p : P) (g : G)
    (decisions : M.DecidesVisibilityProfile a s b d.principalFix T F z p) :
    M.DecidesVisibilityProfile a s b d.principalFix T
      (relationImage F b.carrier (b.graph b (d.iso g))) (a.act s g z) (a.iso g p) := by
  intro w
  obtain ⟨v, rfl⟩ := (d.iso g).surjective w
  have profile := visibilityProfileImage_entry b d F g v
  have visibility := M.act_niceVisibilityName a s t d pairing unions powers separation collection
    carrier maps closed g v
  constructor
  · intro yes
    have moved := a.forcesMem_act s g ((decisions v).1 (profile.1 yes))
    rw [visibility] at moved
    exact moved
  · intro no q qp bad
    have oldq : (a.iso g).symm q ≤ p := by simpa using (a.iso g).symm.monotone qp
    have moved : Name.ForcesMem (a.iso g ((a.iso g).symm q)) (a.act s g z)
        (a.act s g (M.niceVisibilityName a s T (d.principalFix v))) := by
      simpa only [OrderIso.apply_symm_apply, visibility] using bad
    exact (decisions v).2 (fun yes => no (profile.2 yes)) _ oldq
      ((a.forcesMem_act_iff s g _ _ _).1 moved)

end TransitiveGround

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundPreparedMixedCollisions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {L G P : Type u}
variable [Group G] [PartialOrder L] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
variable (closed : ∀ g (tau : Name s), tau.val ∈ T → (a.act s g tau).val ∈ T)
include pairing unions powers separation collection carrier group nodes supports maps hT valid closed

theorem preparedValue_eval_agreement (F B f : ZFSet.{u})
    (z : (M.nameDomain s).names) (p q : P)
    (profile : F ⊆ b.carrier) (basis : B ⊆ F)
    (coinitial : ∀ x ∈ F, ∃ v ∈ B, ZFSet.pair v x ∈ b.conditionOrder)
    (function : ZFSet.IsFunc B (M.niceSupportNameCodes a s T d.principalFix) f)
    (supported : f ⊆ M.niceSupportRelation a s b T d.principalFix)
    (decisions : M.DecidesVisibilityProfile a s b d.principalFix T F z.val p)
    (equalities : ∀ v ∈ B, ∀ tau : Name s,
      tau.val ∈ M.niceSupportNameCodes a s T d.principalFix →
      ZFSet.pair v tau.val ∈ f → Name.ForcesEq p z.val tau)
    (g h : G) (V : L) (relative : g⁻¹ * h ∈ d.principalFix V)
    (qh : q ≤ a.iso h p) (qg : q ≤ a.iso g p)
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily (M.nameDomain s)))
    (hq : H.mem q)
    (visible : Name.eval {r | H.mem r} (a.act s h z.val) ∈
      Name.eval {r | H.mem r} (M.niceVisibilityName a s T (d.principalFix (d.iso h V)))) :
    Name.eval {r | H.mem r} (a.act s h z.val) =
      Name.eval {r | H.mem r} (a.act s g z.val) := by
  have moved := M.decidesVisibilityProfile_act a s t b d pairing unions powers separation
    collection carrier maps closed F z.val p h decisions
  have hz := M.act_mem s a t pairing unions powers separation collection carrier maps h z.val z.property
  have hVisibility := M.niceVisibilityName_mem a s t b d.principalFix pairing unions powers
    separation collection carrier group supports maps hT valid (d.iso h V)
    (M.transitive nodes (b.encode_mem _))
  have member : b.encode V ∈ F := by
    by_contra absent
    have absentImage : b.encode (d.iso h V) ∉
        relationImage F b.carrier (b.graph b (d.iso h)) :=
      fun yes => absent ((visibilityProfileImage_entry b d F h V).1 yes)
    let traveled : (M.nameDomain s).names := ⟨a.act s h z.val, hz⟩
    let vis : (M.nameDomain s).names := ⟨M.niceVisibilityName a s T
      (d.principalFix (d.iso h V)), hVisibility⟩
    have negative : Forces (M.nameDomain s) (.neg (.mem 0 1) : SetFormula 2)
        ![traveled, vis] (a.iso h p) := (moved (d.iso h V)).2 absentImage
    exact (forces_sound (M.nameDomain s) H generic (.neg (.mem 0 1) : SetFormula 2)
      ![traveled, vis] (H.upward hq qh) negative) visible
  obtain ⟨raw, inBasis, lower⟩ := coinitial (b.encode V) member
  obtain ⟨v, rfl⟩ := (b.mem_carrier raw).1 (profile (basis inBasis))
  obtain ⟨code, entry, _⟩ := function.2 (b.encode v) inBasis
  have inCodes := (ZFSet.pair_mem_prod.1 (function.1 entry)).2
  let tau : Name s := ⟨code, M.niceSupportNameCodes_valid a s T d.principalFix code inCodes⟩
  have certificate := (M.pair_mem_niceSupportRelation a s b T d.principalFix v code).1
    (supported entry)
  have fixed : d.principalFix V ≤ a.stabilizer s tau :=
    le_trans (d.principalFix_antitone ((b.pair_mem_conditionOrder v V).1 lower))
      ((niceNameCode_iff a s tau).1 certificate.2).2
  have same : a.act s h tau = a.act s g tau := by
    have fixedName := fixed relative
    change a.act s (g⁻¹ * h) tau = tau at fixedName
    have translated := congrArg (a.act s g) fixedName
    rw [a.act_mul, a.act_inv_right] at translated
    exact translated
  have equality := equalities (b.encode v) inBasis tau inCodes entry
  have atoms : H.GenericFor (Name.atomicFamily (M.nameDomain s)) :=
    fun E hE dense => generic E (Or.inl hE) dense
  have hTau := M.act_mem s a t pairing unions powers separation collection carrier maps h tau certificate.1
  have gTau := M.act_mem s a t pairing unions powers separation collection carrier maps g tau certificate.1
  have gz := M.act_mem s a t pairing unions powers separation collection carrier maps g z.val z.property
  have first := Name.forcesEq_sound (M.nameDomain s) H atoms _ hz _ hTau q hq
    (Name.forcesEq_mono (a.forcesEq_act s h equality) qh)
  have second := Name.forcesEq_sound (M.nameDomain s) H atoms _ gz _ gTau q hq
    (Name.forcesEq_mono (a.forcesEq_act s g equality) qg)
  exact first.trans ((congrArg (Name.eval {r | H.mem r}) same).trans second.symm)

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundPreparedPositionCollisions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (level T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
variable (valid2 : ∀ z ∈ T2, IsName s z)
variable (indices : NiceRefinementIndexSystem M a s b d level T T2 valid valid2)

include indices in
theorem niceRefinementIndex_copies_agree (C E : L) (U Rf Rc : (M.nameDomain s).names)
    (member : refinementIndexCode level (b.encode C) (b.encode E)
      U.val.val Rf.val.val Rc.val.val ∈ M.niceRefinementIndices a s b d level T T2 valid)
    (g h : G) (V : L) (anchor : E ≤ V) (relative : g⁻¹ * h ∈ d.principalFix V) :
    refinementIndexCode level (b.encode (d.iso h C)) (b.encode (d.iso h E))
      (a.act s h U.val).val (a.act s h Rf.val).val (a.act s h Rc.val).val =
    refinementIndexCode level (b.encode (d.iso g C)) (b.encode (d.iso g E))
      (a.act s g U.val).val (a.act s g Rf.val).val (a.act s g Rc.val).val := by
  obtain ⟨lower, hU, hRf, hRc, _⟩ := (indices.typed_entries C E U Rf Rc).1 member
  have point (x : L) (below : x ≤ V) : d.iso h x = d.iso g x := by
    have equal := congrArg (d.iso g) (relative x below)
    rw [d.mul, d.point_inv_right] at equal
    exact equal
  have atC : g⁻¹ * h ∈ d.principalFix C :=
    d.principalFix_antitone (le_trans (le_of_lt lower) anchor) relative
  have name {A : ZFSet.{u}} (tau : Name s)
      (candidate : tau.val ∈ M.niceNameCandidates a s A (d.principalFix C)) :
      a.act s h tau = a.act s g tau := by
    have fixed := ((M.name_mem_niceNameCandidates a s A (d.principalFix C) tau).1 candidate).2.2 atC
    change a.act s (g⁻¹ * h) tau = tau at fixed
    have equal := congrArg (a.act s g) fixed
    rw [a.act_mul, a.act_inv_right] at equal
    exact equal
  rw [point C (le_trans (le_of_lt lower) anchor), point E anchor,
    name U.val hU, name Rf.val hRf, name Rc.val hRc]

end TransitiveGround

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

variable {G L : Type u} [Group G] [PartialOrder L]
variable (a : PosetAction G P) (b : Presentation L) (d : PosetAction G L)
variable (level T2 : ZFSet.{u}) {valid2 : ∀ z ∈ T2, IsName s z}
variable (indices : NiceRefinementIndexSystem M a s b d level T T2 valid valid2)

include indices in
theorem refinementLevelRawCollision_both_orders (C E : L) (U Rf Rc u u' w w' : (M.nameDomain s).names)
    (member : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d level T T2 valid) (p : P)
    (collision : M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid
      Rf Rc u u' w w' p) :
    stageOneRawCollision M (M.refinementLevelFormulaData a s b d level T T2 valid)
      (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
      u.val.val u'.val.val w.val.val w'.val.val (s.encode p) ∧
    stageOneRawCollision M (M.refinementLevelFormulaData a s b d level T T2 valid)
      (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
      u'.val.val u.val.val w'.val.val w.val.val (s.encode p) := by
  refine ⟨(M.refinementLevelRawCollision_iff a s b d level pairing unions powers separation collection
    carrier order hT valid indices C E U Rf Rc u u' w w' member p).2 collision, ?_⟩
  exact (M.refinementLevelRawCollision_iff a s b d level pairing unions powers separation collection
    carrier order hT valid indices C E U Rf Rc u' u w' w member p).2
    (M.stageOneCollisionTest_symm s pairing unions powers separation collection carrier order hT valid
      Rf Rc u u' w w' p collision)

end PartitionPilot.Forcing.TransitiveGround

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

variable (G nodes nodeOrder basis T T2 : ZFSet.{u})

theorem structuralAssignmentActionGraph_branch_entry
    (nodeAction : ZFSet.{u}) {stages history level P order top action x : ZFSet.{u}}
    (function : FunctionGraphOn stages history)
    (stored : ZFSet.pair level (forcingStageCode P order top action) ∈ history)
    (member : x ∈ stageOneAssignments
      (M.rawRefinementFormulaData P order top action G nodes nodeOrder basis T T2 level 0) T)
    (g y : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair g x) y ∈
      M.structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2 stages history ↔
        g ∈ G ∧ ZFSet.pair x y ∈ M.rawStageRefinementAssignmentActionGraph g P order top action
          G nodes nodeOrder nodeAction basis T T2 level := by
  rw [M.pair_mem_structuralAssignmentActionGraph]
  constructor
  · rintro ⟨hg, other, _ho, P', order', top', action', stored', edge⟩
    have bounds := ZFSet.pair_mem_prod.1
      (M.rawStageRefinementAssignmentActionGraph_branch_bound g P' order' top' action'
        G nodes nodeOrder nodeAction basis T T2 other edge)
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ :=
      M.structuralAssignment_branch_unique G nodes nodeOrder basis T T2 function stored stored' member bounds.1
    exact ⟨hg, edge⟩
  · rintro ⟨hg, edge⟩
    exact ⟨hg, level, function.pair_source stored, P, order, top, action, stored, edge⟩

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



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u}
variable [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation I)
variable (T : ZFSet.{u}) (K : I → Subgroup G)

theorem preparedCertificateCode_typed
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (hT : T ∈ M.sets) (validT : ∀ tau ∈ T, IsName s tau)
    (graphGround : M.niceVisibilityGraph a s b T K ∈ M.sets)
    (nodeOrder meet omega : ZFSet.{u}) (z : (M.nameDomain s).names) (p : P)
    (F B f e names : ZFSet.{u})
    (code : PreparedCertificateCode M s.carrier s.conditionOrder (s.encode p)
      b.carrier nodeOrder meet (M.groundRelations T s.carrier)
      (M.niceVisibilityGraph a s b T K) (s.encode ⊤) omega z.val.val F B f e names) :
    M.TypedPreparedCertificate a s b T K nodeOrder meet omega z.val p F B f e names := by
  obtain ⟨filter, basis, nonempty, sync, incidence, raw⟩ := code
  have supported : f ⊆ M.niceSupportRelation a s b T K := by
    intro entry member
    obtain ⟨v, _, tau, _, rfl⟩ := ZFSet.mem_prod.1 (sync.1.1 member)
    rw [← M.visibilitySupportIncidence_eq_niceSupportRelation a s b T K]
    exact incidence v tau member
  have niceRange : f ⊆ ZFSet.prod B (M.niceSupportNameCodes a s T K) := by
    intro entry member
    obtain ⟨v, hv, tau, _, rfl⟩ := ZFSet.mem_prod.1 (sync.1.1 member)
    have nice := ZFSet.pair_mem_prod.1 (ZFSet.mem_sep.1 (supported member)).1
    exact ZFSet.pair_mem_prod.2 ⟨hv, nice.2⟩
  have namesRange : names ⊆ ZFSet.prod omega (M.niceSupportNameCodes a s T K) := by
    intro entry member
    obtain ⟨n, hn, tau, _, rfl⟩ := ZFSet.mem_prod.1 (sync.2.2.1.1 member)
    obtain ⟨v, nv, _⟩ := sync.2.1.2 n hn
    have vt := sync.2.2.2.2.1 n hn v tau nv member
    exact ZFSet.pair_mem_prod.2 ⟨hn, (ZFSet.pair_mem_prod.1 (niceRange vt)).2⟩
  have narrowed : SynchronizedEnumerationCode omega
      (M.niceSupportNameCodes a s T K) B f e names :=
    ⟨⟨niceRange, sync.1.2⟩, sync.2.1, ⟨namesRange, sync.2.2.1.2⟩,
      sync.2.2.2.1, sync.2.2.2.2.1, sync.2.2.2.2.2⟩
  have range : f ⊆ ZFSet.prod b.carrier (M.groundRelations T s.carrier) := by
    intro entry member
    obtain ⟨v, hv, tau, htau, rfl⟩ := ZFSet.mem_prod.1 (sync.1.1 member)
    exact ZFSet.pair_mem_prod.2 ⟨filter.subset (basis.1 hv), htau⟩
  have valid : ∀ tau ∈ M.groundRelations T s.carrier, IsName s tau := by
    intro tau member
    exact Name.isName_of_subset validT ((M.mem_groundRelations T s.carrier tau).1 member).2
  have forcing := (M.preparationForcingCode_iff a s b K pairing unions powers separation
    collection carrier order T (M.groundRelations T s.carrier) graphGround
    (M.groundRelations_mem pairing unions powers separation hT carrier) valid z F f range p).1 raw
  refine ⟨filter, basis, nonempty, narrowed, supported, forcing.1, ?_⟩
  intro v _ tau _ entry
  exact forcing.2 v tau (ZFSet.pair_mem_prod.1 (sync.1.1 entry)).2 entry

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundPreparedStructuralInsertionCollisions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {L G P : Type u}
variable [Group G] [PartialOrder L] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
variable (closed : ∀ g (tau : Name s), tau.val ∈ T → (a.act s g tau).val ∈ T)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)

include group nodes supports hT closed in
theorem prepared_insertion_collision_forces (small : M.sets.Countable)
    (F B f : Fin 2 → ZFSet.{u}) (z y : Fin 2 → (M.nameDomain s).names) (p q : P)
    (profiles : ∀ i, F i ⊆ b.carrier) (bases : ∀ i, B i ⊆ F i)
    (coinitial : ∀ i, ∀ x ∈ F i, ∃ v ∈ B i, ZFSet.pair v x ∈ b.conditionOrder)
    (functions : ∀ i, ZFSet.IsFunc (B i) (M.niceSupportNameCodes a s T d.principalFix) (f i))
    (supported : ∀ i, f i ⊆ M.niceSupportRelation a s b T d.principalFix)
    (decisions : ∀ i, M.DecidesVisibilityProfile a s b d.principalFix T (F i) (z i).val p)
    (equalities : ∀ i, ∀ v ∈ B i, ∀ tau : Name s,
      tau.val ∈ M.niceSupportNameCodes a s T d.principalFix →
      ZFSet.pair v tau.val ∈ f i → Name.ForcesEq p (z i).val tau)
    (h : G) (C K : L) (fixed : h ∈ d.principalFix C)
    (qp : q ≤ p) (qh : q ≤ a.iso h p)
    (good : ∀ i, b.encode C ∉ F i → b.encode K ∉ F i)
    (translatedSupport : ∀ i, d.principalFix K ≤ a.stabilizer s (y i).val)
    (translatedShape : ∀ i, (y i).val.val ⊆ ZFSet.prod T s.carrier)
    (profileTest : Forces (M.nameDomain s) refinementProfileFormula
      ![z 0, z 1, M.stageOneVisibilityName s valid a b d base directed system C] q) :
    let moved := M.stageOneNameAction a s t pairing unions powers separation collection carrier maps
    Forces (M.nameDomain s) refinementCollisionFormula
      ![moved h (z 0), y 0, moved h (z 1), y 1] q →
    Forces (M.nameDomain s) refinementCollisionFormula ![z 0, y 0, z 1, y 1] q := by
  let moved := M.stageOneNameAction a s t pairing unions powers separation collection carrier maps
  dsimp only
  intro referenceTest
  let env : Assignment (M.nameDomain s) 4 := ![z 0, y 0, z 1, y 1]
  let reference : Assignment (M.nameDomain s) 4 := ![moved h (z 0), y 0, moved h (z 1), y 1]
  apply (M.ordinaryForces_iff_all_generics s small carrier refinementCollisionFormula env q).2
  intro H hq generic
  let N : TransitiveGround.{u} := ⟨(M.nameDomain s).values {r | H.mem r},
    (M.nameDomain s).values_transitive _⟩
  let vis (V : L) : (M.nameDomain s).names :=
    M.stageOneVisibilityName s valid a b d base directed system V
  have profileMeaning (i : Fin 2) (V : L) :
      b.encode V ∈ F i ↔ Name.eval {r | H.mem r} (z i).val ∈
        Name.eval {r | H.mem r} (M.niceVisibilityName a s T (d.principalFix V)) := by
    by_cases member : b.encode V ∈ F i
    · have positive : Forces (M.nameDomain s) (.mem 0 1 : SetFormula 2) ![z i, vis V] p :=
        (decisions i V).1 member
      have truth := forces_sound (M.nameDomain s) H generic (.mem 0 1 : SetFormula 2)
        ![z i, vis V] (H.upward hq qp) positive
      exact ⟨fun _ => truth, fun _ => member⟩
    · have negative : Forces (M.nameDomain s) (.neg (.mem 0 1) : SetFormula 2) ![z i, vis V] p :=
        (decisions i V).2 member
      have truth := forces_sound (M.nameDomain s) H generic (.neg (.mem 0 1) : SetFormula 2)
        ![z i, vis V] (H.upward hq qp) negative
      exact ⟨fun yes => False.elim (member yes), fun yes => False.elim (truth yes)⟩
  have pairProfile := (N.realize_refinementProfileFormula
    (evalAssignment {r | H.mem r} ![z 0, z 1, vis C])
    (fun i => ⟨(![z 0, z 1, vis C] : Assignment (M.nameDomain s) 3) i, rfl⟩)).1
    (forces_sound (M.nameDomain s) H generic refinementProfileFormula ![z 0, z 1, vis C]
      hq profileTest)
  change (Name.eval {r | H.mem r} (z 0).val ∈ Name.eval {r | H.mem r}
      (M.niceVisibilityName a s T (d.principalFix C)) ↔
    Name.eval {r | H.mem r} (z 1).val ∈ Name.eval {r | H.mem r}
      (M.niceVisibilityName a s T (d.principalFix C))) at pairProfile
  have pairMembers : b.encode C ∈ F 0 ↔ b.encode C ∈ F 1 :=
    (profileMeaning 0 C).trans (pairProfile.trans (profileMeaning 1 C).symm)
  have referenceCollision := (N.realize_refinementCollisionFormula
    (evalAssignment {r | H.mem r} reference) (fun i => ⟨reference i, rfl⟩)).1
    (forces_sound (M.nameDomain s) H generic refinementCollisionFormula reference hq referenceTest)
  change (Name.eval {r | H.mem r} (moved h (z 0)).val = Name.eval {r | H.mem r} (y 0).val ↔
    Name.eval {r | H.mem r} (moved h (z 1)).val = Name.eval {r | H.mem r} (y 1).val)
      at referenceCollision
  apply (N.realize_refinementCollisionFormula (evalAssignment {r | H.mem r} env)
    (fun i => ⟨env i, rfl⟩)).2
  change (Name.eval {r | H.mem r} (z 0).val = Name.eval {r | H.mem r} (y 0).val ↔
    Name.eval {r | H.mem r} (z 1).val = Name.eval {r | H.mem r} (y 1).val)
  by_cases member : b.encode C ∈ F 0
  · have both : ∀ i, b.encode C ∈ F i :=
      fun i => Fin.cases member (fun j => Fin.cases (pairMembers.1 member) (fun k => Fin.elim0 k) j) i
    have same (i : Fin 2) : Name.eval {r | H.mem r} (z i).val =
        Name.eval {r | H.mem r} (moved h (z i)).val := by
      have relative : h⁻¹ * 1 ∈ d.principalFix C := by
        simpa only [mul_one] using (d.principalFix C).inv_mem fixed
      have visible : Name.eval {r | H.mem r} (a.act s 1 (z i).val) ∈
          Name.eval {r | H.mem r} (M.niceVisibilityName a s T (d.principalFix (d.iso 1 C))) := by
        simpa only [a.act_one, d.one] using (profileMeaning i C).1 (both i)
      have result := M.preparedValue_eval_agreement a s t b d pairing unions powers separation
        collection carrier group nodes supports maps hT valid closed (F i) (B i) (f i) (z i)
        p q (profiles i) (bases i) (coinitial i) (functions i) (supported i) (decisions i)
        (equalities i) h 1 C relative (by simpa only [a.one] using qp) qh H generic hq visible
      simpa only [a.act_one, moved, stageOneNameAction_val] using result
    exact ⟨fun first => (same 1).trans (referenceCollision.1 ((same 0).symm.trans first)),
      fun second => (same 0).trans (referenceCollision.2 ((same 1).symm.trans second))⟩
  · have absent : ∀ i, b.encode C ∉ F i :=
      fun i => Fin.cases member (fun j => Fin.cases (fun yes => member (pairMembers.2 yes)) (fun k => Fin.elim0 k) j) i
    have different (i : Fin 2) : Name.eval {r | H.mem r} (z i).val ≠
        Name.eval {r | H.mem r} (y i).val := by
      intro equal
      have visible := system.normalization_visible K (y i) (translatedSupport i) H generic
        (Name.eval_subset_familySet_of_code_subset H T valid (y i).val (translatedShape i))
      exact good i (absent i) ((profileMeaning i K).2 (equal.symm ▸ visible))
    exact ⟨fun first => False.elim (different 0 first), fun second => False.elim (different 1 second)⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u

private theorem anchor_of_dataBound_p1 {L : Type u} [PartialOrder L]
    (b : Presentation L) (I level T S mu X tuples A : ZFSet.{u})
    (C E D : L) (U Rf Rc u w : ZFSet.{u})
    (bound : ZFSet.pair (stageOneAssignment
      (refinementIndexCode level (b.encode C) (b.encode E) U Rf Rc) u w) (b.encode D) ∈
      stageOneDataBounds A I T S b.carrier mu X b.conditionOrder
        (refinementIndexFieldGraph I b.carrier 2) tuples) : E ≤ D := by
  obtain ⟨_, _, _, _, _, rawE, _, fu, _hfu, fw, _hfw, edge, lower, _rest⟩ :=
    (stageOneDataBounds_assignment_entry A I T S b.carrier mu X b.conditionOrder
      (refinementIndexFieldGraph I b.carrier 2) tuples _ u w (b.encode D)).1 bound
  have same : rawE = b.encode E :=
    ((refinementIndexFieldGraph_entry I b.carrier ![level, b.encode C, b.encode E, U, Rf, Rc]
      2 rawE).1 edge).2.2
  subst rawE
  exact (b.pair_mem_conditionOrder E D).1 lower

variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (level T T2 : ZFSet.{u})
variable (system : RefinementStageSystem M a s t b d base directed level T T2)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (hLevel : level ∈ M.sets) (hT : T ∈ M.sets)
include system pairing unions powers separation collection carrier order group nodes supports hLevel hT

theorem structuralAssignment_insertion_reference
    {stages history : ZFSet.{u}} (function : FunctionGraphOn stages history)
    (stored : ZFSet.pair level (forcingStageCode s.carrier s.conditionOrder (s.encode ⊤)
      (a.actionGraph s t)) ∈ history)
    (I S mu positions tuples sourceA : ZFSet.{u})
    (h : G) (D K V C E : L) (U Rf Rc : (M.nameDomain s).names) (u w : Name s)
    (index : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d level T T2 system.valid1)
    (hu : u.val ∈ T) (hw : w.val ∈ T)
    (source : stageOneAssignment
      (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
      u.val w.val ∈ sourceA)
    (newU newW : ZFSet.{u})
    (bound : ZFSet.pair (stageOneAssignment
      (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
      newU newW) (b.encode (d.iso h D)) ∈ stageOneDataBounds
        (M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
          (supportBasisCode b t d.principalFix) T T2 stages history (t.encode h) sourceA)
        I T S b.carrier mu positions b.conditionOrder (refinementIndexFieldGraph I b.carrier 2) tuples)
    (cap : d.iso h D ≤ K) (avoid : E ≤ K → E ≤ V) (fixed : h ∈ d.principalFix V) :
    E ≤ V ∧
    refinementIndexCode level (b.encode (d.iso h C)) (b.encode (d.iso h E))
      (a.act s h U.val).val (a.act s h Rf.val).val (a.act s h Rc.val).val =
      refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∧
    ZFSet.pair (ZFSet.pair (t.encode h) (stageOneAssignment
      (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val) u.val w.val))
      (stageOneAssignment
        (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
        (a.act s h u).val (a.act s h w).val) ∈
      M.structuralAssignmentActionGraph t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 stages history ∧
    stageOneAssignment
      (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
      (a.act s h u).val (a.act s h w).val ∈
      M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 stages history (t.encode h) sourceA := by
  let image := M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 stages history (t.encode h) sourceA
  have below : E ≤ d.iso h D := anchor_of_dataBound_p1 b I level T S mu positions tuples image
    C E (d.iso h D) U.val.val Rf.val.val Rc.val.val newU newW bound
  have anchor := avoid (below.trans cap)
  have same := M.niceRefinementIndex_copies_agree a s b d level T T2 system.valid1 system.valid2
    system.indices C E U Rf Rc index 1 h V anchor (by simpa only [inv_one, one_mul] using fixed)
  simp only [d.one, a.act_one] at same
  let idx := refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
  let z := stageOneAssignment idx u.val w.val
  let target := stageOneAssignment idx (a.act s h u).val (a.act s h w).val
  have dataEq := M.rawRefinementFormulaData_eq a s t b d pairing unions powers separation collection
    carrier group nodes supports system.inputs.condition_maps level T T2 system.valid1 system.valid2
  have branchMember : z ∈ stageOneAssignments
      (M.rawRefinementFormulaData s.carrier s.conditionOrder (s.encode ⊤) (a.actionGraph s t)
        t.carrier b.carrier b.conditionOrder (supportBasisCode b t d.principalFix) T T2 level 0) T := by
    rw [dataEq]
    exact (stageOneAssignment_mem_assignments _ _ _ _ _).2 ⟨index, hu, hw⟩
  have graphEq := M.rawStageRefinementAssignmentActionGraph_eq a s t b d pairing unions powers
    separation collection carrier group nodes order system.inputs.condition_maps system.inputs.node_maps
    supports level T T2 hLevel hT system.valid1 system.valid2 system.inputs.terms_closed
    system.inputs.pairs_closed system.inputs.family_ground system.indices.index_ground
  have branch := (M.refinementAssignmentActionGraph_entry a s b d level T T2 system.valid1
    system.valid2 system.inputs.terms_closed t pairing unions powers separation collection carrier
    order system.inputs.condition_maps system.inputs.pairs_closed system.inputs.family_ground
    h C E U Rf Rc u w index hu hw target).2
      (congrArg (fun i => stageOneAssignment i (a.act s h u).val (a.act s h w).val) same.symm)
  rw [← graphEq h] at branch
  have edge := (M.structuralAssignmentActionGraph_branch_entry t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 (d.actionGraph b t) function stored
    branchMember (t.encode h) target).2 ⟨t.encode_mem h, branch⟩
  exact ⟨anchor, same, edge,
    (M.structuralAssignmentImage_entry t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 stages history (t.encode h) sourceA target).2
      ⟨z, source, edge⟩⟩

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (level T T2 : ZFSet.{u})
variable (system : RefinementStageSystem M a s t b d base directed level T T2)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (hLevel : level ∈ M.sets) (hT : T ∈ M.sets)
include system pairing unions powers separation collection carrier order group nodes supports hLevel hT

theorem structuralAssignment_prepared_insertion_collision_oai
    (small : M.sets.Countable)
    {stages history : ZFSet.{u}} (function : FunctionGraphOn stages history)
    (stored : ZFSet.pair level (forcingStageCode s.carrier s.conditionOrder (s.encode ⊤)
      (a.actionGraph s t)) ∈ history)
    (I S mu positions tuples sourceA : ZFSet.{u})
    (positionSupport : ∀ (D : L), ∀ f ∈ S, ∀ u : Name s, ZFSet.pair f u.val ∈ tuples →
      RowPositionBound mu positions b.conditionOrder f (b.encode D) →
      d.principalFix D ≤ a.stabilizer s u)
    (h : G) (D K V C E : L) (U Rf Rc u w newU newW : (M.nameDomain s).names)
    (index : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d level T T2 system.valid1)
    (hu : u.val.val ∈ T) (hw : w.val.val ∈ T)
    (hNewU : newU.val.val ∈ T) (hNewW : newW.val.val ∈ T)
    (p q : P) (qp : q ≤ p) (qh : q ≤ a.iso h p)
    (fixed : h ∈ d.principalFix V) (cap : d.iso h D ≤ K)
    (avoid : E ≤ K → E ≤ V) (F B f e names : Fin 2 → ZFSet.{u})
    (good : ∀ i, b.encode V ∉ F i → b.encode K ∉ F i) :
    let fields := M.refinementLevelFormulaData a s b d level T T2 system.valid1
    let image := M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 stages history (t.encode h) sourceA
    let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT system.valid1
    let idx := refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
    stageOneAssignment idx u.val.val w.val.val ∈ sourceA →
    ZFSet.pair (stageOneAssignment idx newU.val.val newW.val.val) (b.encode (d.iso h D)) ∈
      stageOneDataBounds image I T S b.carrier mu positions b.conditionOrder
        (refinementIndexFieldGraph I b.carrier 2) tuples →
    stageOneRawTests M fields sourceA (s.encode p) → stageOneRawTests M fields image (s.encode q) →
    (∀ i : Fin 2, PreparedCertificateCode M s.carrier s.conditionOrder (s.encode p)
      b.carrier b.conditionOrder (canonicalMeetGraph b.carrier b.conditionOrder)
      (M.groundRelations T s.carrier) (M.niceVisibilityGraph a s b T d.principalFix) (s.encode ⊤)
      ZFSet.omega ((![cls Rc u, cls Rf w] : Fin 2 → (M.nameDomain s).names) i).val.val
      (F i) (B i) (f i) (e i) (names i)) →
    E ≤ V ∧
    stageOneRawCollision M fields idx u.val.val newU.val.val w.val.val newW.val.val (s.encode q) ∧
    stageOneRawCollision M fields idx newU.val.val u.val.val newW.val.val w.val.val (s.encode q) := by
  let fields := M.refinementLevelFormulaData a s b d level T T2 system.valid1
  let image := M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 stages history (t.encode h) sourceA
  let moved := M.stageOneNameAction a s t pairing unions powers separation collection carrier system.inputs.condition_maps
  let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT system.valid1
  let idx := refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
  let original : Fin 2 → (M.nameDomain s).names := ![cls Rc u, cls Rf w]
  let translated : Fin 2 → (M.nameDomain s).names := ![cls Rc newU, cls Rf newW]
  dsimp only
  intro source bound sourceTests translatedTests certificates
  have reference := M.structuralAssignment_insertion_reference a s t b d base directed level T T2
    system pairing unions powers separation collection carrier order group nodes supports hLevel hT
    function stored I S mu positions tuples sourceA h D K V C E U Rf Rc u.val w.val index hu hw
    source newU.val.val newW.val.val bound cap avoid fixed
  have parts := (refinementIndexCode_eq_iff _ _ _ _ _ _ _ _ _ _ _ _).1 reference.2.1
  have fine : moved h Rf = Rf := Subtype.ext (Subtype.ext parts.2.2.2.2.1)
  have coarse : moved h Rc = Rc := Subtype.ext (Subtype.ext parts.2.2.2.2.2)
  obtain ⟨newMember, _, _, _, _, rawE, _, fu, hfu, fw, hfw, anchorEdge, below,
      tu, tw, bu, bw⟩ :=
    (stageOneDataBounds_assignment_entry image I T S b.carrier mu positions b.conditionOrder
      (refinementIndexFieldGraph I b.carrier 2) tuples idx newU.val.val newW.val.val
      (b.encode (d.iso h D))).1 bound
  have sameAnchor : rawE = b.encode E :=
    ((refinementIndexFieldGraph_entry I b.carrier
      ![level, b.encode C, b.encode E, U.val.val, Rf.val.val, Rc.val.val] 2 rawE).1 anchorEdge).2.2
  have belowCap : E ≤ K := ((b.pair_mem_conditionOrder E (d.iso h D)).1 (sameAnchor ▸ below)).trans cap
  have positions : ∀ i : Fin 2, d.principalFix K ≤
      a.stabilizer s ((![newU, newW] : Fin 2 → (M.nameDomain s).names) i).val := by
    have first := le_trans (d.principalFix_antitone cap)
      (positionSupport (d.iso h D) fu hfu newU.val tu bu)
    have second := le_trans (d.principalFix_antitone cap)
      (positionSupport (d.iso h D) fw hfw newW.val tw bw)
    exact Fin.cases first (Fin.cases second (fun j => Fin.elim0 j))
  have classes := M.niceRefinementClasses_supported_by_block a s b d level T T2
    system.valid1 system.valid2 system.indices base directed system.inputs.terms_closed system.terms_hs
    C E K U Rf Rc index belowCap ![newU.val, newW.val]
      (Fin.cases (positions 0) (Fin.cases (positions 1) (fun j => Fin.elim0 j)))
  have single := (M.refinementLevelRawSingle_iff a s b d level pairing unions powers separation collection
    carrier order nodes hT system.valid1 system.indices base directed system.first C E U Rf Rc u w index p).1
    (sourceTests.1 idx index u.val.val hu w.val.val hw source)
  have profile : Forces (M.nameDomain s) refinementProfileFormula
      ![original 0, original 1, M.stageOneVisibilityName s system.valid1 a b d base directed system.first V] q :=
    forces_mono (M.nameDomain s) _ _ (single.2.1 V reference.1) qp
  have referenceRaw := translatedTests.2 idx index
    (moved h u).val.val (system.inputs.terms_closed h u.val hu) newU.val.val hNewU
    (moved h w).val.val (system.inputs.terms_closed h w.val hw) newW.val.val hNewW
    reference.2.2.2 newMember
  have referenceTyped := (M.refinementLevelRawCollision_iff a s b d level pairing unions powers separation
    collection carrier order hT system.valid1 system.indices C E U Rf Rc
    (moved h u) newU (moved h w) newW index q).1 referenceRaw
  have classLaw (R v : (M.nameDomain s).names) : moved h (cls R v) = cls (moved h R) (moved h v) :=
    M.stageOneNameAction_class a s t pairing unions powers separation collection carrier
      system.inputs.condition_maps order hT system.valid1 system.inputs.terms_closed h R v
  have referenceFormula : Forces (M.nameDomain s) refinementCollisionFormula
      ![moved h (original 0), translated 0, moved h (original 1), translated 1] q := by
    change Forces (M.nameDomain s) refinementCollisionFormula
      ![moved h (cls Rc u), cls Rc newU, moved h (cls Rf w), cls Rf newW] q
    rw [classLaw Rc u, classLaw Rf w, fine, coarse]
    exact referenceTyped
  have recognized (i : Fin 2) := M.preparedCertificateCode_typed a s b T d.principalFix pairing unions powers
    separation collection carrier order hT system.valid1 system.first.visibility_graph_ground
    b.conditionOrder (canonicalMeetGraph b.carrier b.conditionOrder) ZFSet.omega
    (original i) p (F i) (B i) (f i) (e i) (names i) (certificates i)
  have forced := M.prepared_insertion_collision_forces a s t b d pairing unions powers separation collection
    carrier group nodes supports system.inputs.condition_maps hT system.valid1 system.inputs.terms_closed
    base directed system.first small F B f original translated p q
    (fun i => (recognized i).1.subset) (fun i => (recognized i).2.1.1)
    (fun i => (recognized i).2.1.2) (fun i => (recognized i).2.2.2.1.1)
    (fun i => (recognized i).2.2.2.2.1) (fun i => (recognized i).2.2.2.2.2.1)
    (fun i => (recognized i).2.2.2.2.2.2) h V K fixed qp qh good
    (Fin.cases (classes 0).1 (Fin.cases (classes 1).1 (fun j => Fin.elim0 j)))
    (Fin.cases (Name.refinementClass_subset T system.valid1 Rc.val newU.val)
      (Fin.cases (Name.refinementClass_subset T system.valid1 Rf.val newW.val) (fun j => Fin.elim0 j)))
    profile referenceFormula
  have typed : M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT system.valid1
      Rf Rc u newU w newW q := forced
  exact ⟨reference.1, M.refinementLevelRawCollision_both_orders s pairing unions powers separation collection
    carrier order hT system.valid1 a b d level T2 system.indices C E U Rf Rc u newU w newW index q typed⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

theorem solution.{u} : type_of% @OAI.PartitionPilot.Forcing.TransitiveGround.structuralAssignment_prepared_insertion_collision_oai.{u} := @OAI.PartitionPilot.Forcing.TransitiveGround.structuralAssignment_prepared_insertion_collision_oai.{u}
