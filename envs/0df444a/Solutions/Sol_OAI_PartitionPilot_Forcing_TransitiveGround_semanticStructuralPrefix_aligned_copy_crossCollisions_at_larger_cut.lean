-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefix_aligned_copy_crossCollisions_at_larger_cut
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:33:45.488731+00:00
-- url     : https://prove2.me/submissions/f9186967-289b-40c7-ab9d-8ef5d6e52c4e

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
import Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_semanticStructuralPrefix_aligned_cut_tests_at_larger_cut
import Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_semanticStructuralPrefix_typed_assignment_certificates

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

theorem ordinaryForces_iff_all_joint_generics (small : M.sets.Countable)
    (carrier : s.carrier ∈ M.sets) {n : Nat} (phi : SetFormula n)
    (env : Assignment (M.nameDomain s) n) (p : P) :
    Forces (M.nameDomain s) phi env p ↔
      ∀ H : ConditionFilter P, H.mem p → H.GenericFor (M.codedFamily s) →
        H.GenericFor (formulaFamily (M.nameDomain s)) →
        Realize ((M.nameDomain s).values {q | H.mem q}) phi
          (evalAssignment {q | H.mem q} env) := by
  constructor
  · intro forced H member _ generic
    exact forces_sound (M.nameDomain s) H generic phi env member forced
  · intro truth
    by_contra bad
    obtain ⟨q, below, negative⟩ := not_forces_refine_neg (M.nameDomain s) phi env bad
    obtain ⟨H, member, coded, ordinary⟩ := M.exists_coded_ordinary_generic s small carrier q
    exact (forces_sound (M.nameDomain s) H ordinary (.neg phi) env member negative)
      (truth H (H.upward member below) coded ordinary)

end TransitiveGround



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
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L)
variable (d : PosetAction G L) (base : L)
variable (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
variable (system : NiceNameSystem M a s b d base directed T valid)
variable (H : ConditionFilter P)
variable (generic : H.GenericFor (formulaFamily (M.nameDomain s)))
variable (meet : L → L → L)
variable (descent : ∀ (v w : L) (x y : (M.nameDomain s).names),
  d.principalFix v ≤ a.stabilizer s x.val →
  d.principalFix w ≤ a.stabilizer s y.val →
  HereditarilySymmetric a s (d.principalSupportFamily base directed) x.val →
  HereditarilySymmetric a s (d.principalSupportFamily base directed) y.val →
  Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
  ∃ τ : (M.nameDomain s).names,
    HereditarilySymmetric a s (d.principalSupportFamily base directed) τ.val ∧
    d.principalFix (meet v w) ≤ a.stabilizer s τ.val ∧
    Name.eval {p | H.mem p} τ.val = Name.eval {p | H.mem p} x.val)

include system generic descent in
theorem common_value_visible (A B : L) (x y : (M.nameDomain s).names)
    (sx : d.principalFix A ≤ a.stabilizer s x.val)
    (sy : d.principalFix B ≤ a.stabilizer s y.val)
    (hx : HereditarilySymmetric a s (d.principalSupportFamily base directed) x.val)
    (hy : HereditarilySymmetric a s (d.principalSupportFamily base directed) y.val)
    (subset : Name.eval {p | H.mem p} x.val ⊆
      Name.eval {p | H.mem p} (Name.familySet ⊤ T valid))
    (values : Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val) :
    Name.eval {p | H.mem p} x.val ∈
      Name.eval {p | H.mem p} (M.niceVisibilityName a s T (d.principalFix (meet A B))) := by
  obtain ⟨τ, _, support, equal⟩ := descent A B x y sx sy hx hy values
  have bounded : Name.eval {p | H.mem p} τ.val ⊆
      Name.eval {p | H.mem p} (Name.familySet ⊤ T valid) := equal.symm ▸ subset
  exact equal ▸ system.normalization_visible (meet A B) τ support H generic bounded

include generic descent in
theorem mixed_collision_visible_both (A B : L)
    (x y : Fin 2 → (M.nameDomain s).names)
    (sx : ∀ i, d.principalFix A ≤ a.stabilizer s (x i).val)
    (sy : ∀ i, d.principalFix B ≤ a.stabilizer s (y i).val)
    (hx : ∀ i, HereditarilySymmetric a s (d.principalSupportFamily base directed) (x i).val)
    (hy : ∀ i, HereditarilySymmetric a s (d.principalSupportFamily base directed) (y i).val)
    (subset : ∀ i, Name.eval {p | H.mem p} (x i).val ⊆
      Name.eval {p | H.mem p} (Name.familySet ⊤ T valid))
    (q : P) (hq : H.mem q)
    (profile : Forces (M.nameDomain s) refinementProfileFormula
      ![x 0, x 1, M.stageOneVisibilityName s valid a b d base directed system (meet A B)] q)
    (collision : Name.eval {p | H.mem p} (x 0).val = Name.eval {p | H.mem p} (y 0).val ∨
      Name.eval {p | H.mem p} (x 1).val = Name.eval {p | H.mem p} (y 1).val) :
    ∀ i, Name.eval {p | H.mem p} (x i).val ∈
      Name.eval {p | H.mem p} (M.niceVisibilityName a s T (d.principalFix (meet A B))) := by
  let env : Assignment (M.nameDomain s) 3 :=
    ![x 0, x 1, M.stageOneVisibilityName s valid a b d base directed system (meet A B)]
  let N : TransitiveGround.{u} := ⟨(M.nameDomain s).values {p | H.mem p},
    (M.nameDomain s).values_transitive _⟩
  have realized := forces_sound (M.nameDomain s) H generic refinementProfileFormula env hq profile
  have paired := (N.realize_refinementProfileFormula (evalAssignment {p | H.mem p} env)
    (fun i => ⟨env i, rfl⟩)).1 realized
  change (Name.eval {p | H.mem p} (x 0).val ∈
      Name.eval {p | H.mem p} (M.niceVisibilityName a s T (d.principalFix (meet A B)))) ↔
    (Name.eval {p | H.mem p} (x 1).val ∈
      Name.eval {p | H.mem p} (M.niceVisibilityName a s T (d.principalFix (meet A B)))) at paired
  have one (i : Fin 2)
      (equal : Name.eval {p | H.mem p} (x i).val = Name.eval {p | H.mem p} (y i).val) :=
    M.common_value_visible a s b d base directed T valid system H generic meet descent
      A B (x i) (y i) (sx i) (sy i) (hx i) (hy i) (subset i) equal
  rcases collision with left | right
  · have first := one 0 left
    exact Fin.cases first (Fin.cases (paired.1 first) (fun i => Fin.elim0 i))
  · have second := one 1 right
    exact Fin.cases (paired.2 second) (Fin.cases second (fun i => Fin.elim0 i))

end PartitionPilot.Forcing.TransitiveGround

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
variable (meet : L → L → L)
variable (descent : ∀ (H : ConditionFilter P),
  H.GenericFor (M.codedFamily s) →
  H.GenericFor (formulaFamily (M.nameDomain s)) →
  ∀ (v w : L) (x y : (M.nameDomain s).names),
    d.principalFix v ≤ a.stabilizer s x.val →
    d.principalFix w ≤ a.stabilizer s y.val →
    HereditarilySymmetric a s (d.principalSupportFamily base directed) x.val →
    HereditarilySymmetric a s (d.principalSupportFamily base directed) y.val →
    Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
    ∃ tau : (M.nameDomain s).names,
      HereditarilySymmetric a s (d.principalSupportFamily base directed) tau.val ∧
      d.principalFix (meet v w) ≤ a.stabilizer s tau.val ∧
      Name.eval {p | H.mem p} tau.val = Name.eval {p | H.mem p} x.val)

include group nodes supports hT closed descent in
theorem prepared_joint_mixed_collision_forces (small : M.sets.Countable)
    (F B f : Fin 2 → ZFSet.{u}) (z y : Fin 2 → (M.nameDomain s).names) (p q : P)
    (profiles : ∀ i, F i ⊆ b.carrier) (bases : ∀ i, B i ⊆ F i)
    (coinitial : ∀ i, ∀ x ∈ F i, ∃ v ∈ B i, ZFSet.pair v x ∈ b.conditionOrder)
    (functions : ∀ i, ZFSet.IsFunc (B i) (M.niceSupportNameCodes a s T d.principalFix) (f i))
    (supported : ∀ i, f i ⊆ M.niceSupportRelation a s b T d.principalFix)
    (decisions : ∀ i, M.DecidesVisibilityProfile a s b d.principalFix T (F i) (z i).val p)
    (equalities : ∀ i, ∀ v ∈ B i, ∀ tau : Name s,
      tau.val ∈ M.niceSupportNameCodes a s T d.principalFix →
      ZFSet.pair v tau.val ∈ f i → Name.ForcesEq p (z i).val tau)
    (g h : G) (V A X : L) (relative : g⁻¹ * h ∈ d.principalFix V)
    (qh : q ≤ a.iso h p) (qg : q ≤ a.iso g p) (overlap : meet A X = d.iso h V) :
    let moved := M.stageOneNameAction a s t pairing unions powers separation collection carrier maps
    ∀ (_newSupport : ∀ i, d.principalFix A ≤ a.stabilizer s (moved h (z i)).val)
      (_oldSupport : ∀ i, d.principalFix X ≤ a.stabilizer s (y i).val)
      (_newHS : ∀ i, HereditarilySymmetric a s (d.principalSupportFamily base directed)
        (moved h (z i)).val)
      (_oldHS : ∀ i, HereditarilySymmetric a s (d.principalSupportFamily base directed) (y i).val)
      (_shape : ∀ i, (moved h (z i)).val.val ⊆ ZFSet.prod T s.carrier)
      (_profileTest : Forces (M.nameDomain s) refinementProfileFormula
        ![moved h (z 0), moved h (z 1),
          M.stageOneVisibilityName s valid a b d base directed system (d.iso h V)] q)
      (_referenceTest : Forces (M.nameDomain s) refinementCollisionFormula
        ![moved g (z 0), y 0, moved g (z 1), y 1] q),
      Forces (M.nameDomain s) refinementCollisionFormula
        ![moved h (z 0), y 0, moved h (z 1), y 1] q := by
  let moved := M.stageOneNameAction a s t pairing unions powers separation collection carrier maps
  dsimp only
  intro newSupport oldSupport newHS oldHS shape profileTest referenceTest
  let env : Assignment (M.nameDomain s) 4 := ![moved h (z 0), y 0, moved h (z 1), y 1]
  let reference : Assignment (M.nameDomain s) 4 := ![moved g (z 0), y 0, moved g (z 1), y 1]
  apply (M.ordinaryForces_iff_all_joint_generics s small carrier refinementCollisionFormula env q).2
  intro H hq coded generic
  let N : TransitiveGround.{u} := ⟨(M.nameDomain s).values {r | H.mem r},
    (M.nameDomain s).values_transitive _⟩
  have old := (N.realize_refinementCollisionFormula (evalAssignment {r | H.mem r} reference)
    (fun i => ⟨reference i, rfl⟩)).1
    (forces_sound (M.nameDomain s) H generic refinementCollisionFormula reference hq referenceTest)
  change (Name.eval {r | H.mem r} (moved g (z 0)).val = Name.eval {r | H.mem r} (y 0).val ↔
    Name.eval {r | H.mem r} (moved g (z 1)).val = Name.eval {r | H.mem r} (y 1).val) at old
  have agreement
      (collision : Name.eval {r | H.mem r} (moved h (z 0)).val = Name.eval {r | H.mem r} (y 0).val ∨
        Name.eval {r | H.mem r} (moved h (z 1)).val = Name.eval {r | H.mem r} (y 1).val) :
      ∀ i, Name.eval {r | H.mem r} (moved h (z i)).val =
        Name.eval {r | H.mem r} (moved g (z i)).val := by
    have bounded (i : Fin 2) := Name.eval_subset_familySet_of_code_subset H T valid
      (moved h (z i)).val (shape i)
    have overlapProfile : Forces (M.nameDomain s) refinementProfileFormula
        ![moved h (z 0), moved h (z 1),
          M.stageOneVisibilityName s valid a b d base directed system (meet A X)] q :=
      overlap.symm ▸ profileTest
    have visible := M.mixed_collision_visible_both a s b d base directed T valid system H generic
      meet (descent H coded generic) A X (fun i => moved h (z i)) y newSupport oldSupport newHS oldHS
      bounded q hq overlapProfile collision
    intro i
    have atOverlap : Name.eval {r | H.mem r} (a.act s h (z i).val) ∈
        Name.eval {r | H.mem r} (M.niceVisibilityName a s T (d.principalFix (d.iso h V))) :=
      overlap ▸ visible i
    exact M.preparedValue_eval_agreement a s t b d pairing unions powers separation collection
      carrier group nodes supports maps hT valid closed (F i) (B i) (f i) (z i) p q (profiles i)
      (bases i) (coinitial i) (functions i) (supported i) (decisions i) (equalities i)
      g h V relative qh qg H generic hq atOverlap
  apply (N.realize_refinementCollisionFormula (evalAssignment {r | H.mem r} env)
    (fun i => ⟨env i, rfl⟩)).2
  change (Name.eval {r | H.mem r} (moved h (z 0)).val = Name.eval {r | H.mem r} (y 0).val ↔
    Name.eval {r | H.mem r} (moved h (z 1)).val = Name.eval {r | H.mem r} (y 1).val)
  constructor
  · intro first
    have equal := agreement (Or.inl first)
    exact (equal 1).trans (old.1 ((equal 0).symm.trans first))
  · intro second
    have equal := agreement (Or.inr second)
    exact (equal 0).trans (old.2 ((equal 1).symm.trans second))

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

namespace TransitiveGround
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
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (group : t.carrier ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
variable (closed : ∀ g (tau : Name s), tau.val ∈ T → (a.act s g tau).val ∈ T)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)
variable (meet : L → L → L)
variable (descent : ∀ (H : ConditionFilter P),
  H.GenericFor (M.codedFamily s) →
  H.GenericFor (formulaFamily (M.nameDomain s)) →
  ∀ (v w : L) (x y : (M.nameDomain s).names),
    d.principalFix v ≤ a.stabilizer s x.val →
    d.principalFix w ≤ a.stabilizer s y.val →
    HereditarilySymmetric a s (d.principalSupportFamily base directed) x.val →
    HereditarilySymmetric a s (d.principalSupportFamily base directed) y.val →
    Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
    ∃ tau : (M.nameDomain s).names,
      HereditarilySymmetric a s (d.principalSupportFamily base directed) tau.val ∧
      d.principalFix (meet v w) ≤ a.stabilizer s tau.val ∧
      Name.eval {p | H.mem p} tau.val = Name.eval {p | H.mem p} x.val)

variable {T2 : ZFSet.{u}} (valid2 : ∀ z ∈ T2, IsName s z)
variable (closed2 : ∀ g (tau : Name s), tau.val ∈ T2 → (a.act s g tau).val ∈ T2)
variable (level : ZFSet.{u})
variable (indices : NiceRefinementIndexSystem M a s b d level T T2 valid valid2)

include group nodes supports closed closed2 descent indices in
theorem prepared_joint_refinementCollision_tests (small : M.sets.Countable)
    (C E : L) (U Rf Rc u w oldU oldW : (M.nameDomain s).names)
    (member : refinementIndexCode level (b.encode C) (b.encode E)
      U.val.val Rf.val.val Rc.val.val ∈ M.niceRefinementIndices a s b d level T T2 valid)
    (F B f : Fin 2 → ZFSet.{u}) (p q : P) (g h : G) (V A X : L)
    (relative : g⁻¹ * h ∈ d.principalFix V)
    (qh : q ≤ a.iso h p) (qg : q ≤ a.iso g p)
    (overlap : meet A X = d.iso h V) (anchor : d.iso h E ≤ meet A X) :
    let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
    let moved := M.stageOneNameAction a s t pairing unions powers separation collection carrier maps
    let original := ![cls Rc u, cls Rf w]
    let newPair := ![cls (moved h Rc) (moved h u), cls (moved h Rf) (moved h w)]
    let oldPair := ![cls (moved h Rc) oldU, cls (moved h Rf) oldW]
    ∀ (_profiles : ∀ i, F i ⊆ b.carrier) (_bases : ∀ i, B i ⊆ F i)
      (_coinitial : ∀ i, ∀ x ∈ F i, ∃ v ∈ B i, ZFSet.pair v x ∈ b.conditionOrder)
      (_functions : ∀ i, ZFSet.IsFunc (B i) (M.niceSupportNameCodes a s T d.principalFix) (f i))
      (_supported : ∀ i, f i ⊆ M.niceSupportRelation a s b T d.principalFix)
      (_decisions : ∀ i, M.DecidesVisibilityProfile a s b d.principalFix T (F i) (original i).val p)
      (_equalities : ∀ i, ∀ v ∈ B i, ∀ tau : Name s,
        tau.val ∈ M.niceSupportNameCodes a s T d.principalFix →
        ZFSet.pair v tau.val ∈ f i → Name.ForcesEq p (original i).val tau)
      (_newSupport : ∀ i, d.principalFix A ≤ a.stabilizer s (newPair i).val)
      (_oldSupport : ∀ i, d.principalFix X ≤ a.stabilizer s (oldPair i).val)
      (_newHS : ∀ i, HereditarilySymmetric a s (d.principalSupportFamily base directed) (newPair i).val)
      (_oldHS : ∀ i, HereditarilySymmetric a s (d.principalSupportFamily base directed) (oldPair i).val)
      (_single : M.stageOneSingleTests s pairing unions powers separation collection carrier order hT valid
        a b d base directed system C E U Rf Rc u w p)
      (_reference : M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid
        (moved h Rf) (moved h Rc) (moved g u) oldU (moved g w) oldW q),
      M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid
        (moved h Rf) (moved h Rc) (moved h u) oldU (moved h w) oldW q ∧
      stageOneRawCollision M (M.refinementLevelFormulaData a s b d level T T2 valid)
        (refinementIndexCode level (b.encode (d.iso h C)) (b.encode (d.iso h E))
          (moved h U).val.val (moved h Rf).val.val (moved h Rc).val.val)
        (moved h u).val.val oldU.val.val (moved h w).val.val oldW.val.val (s.encode q) := by
  let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
  let moved := M.stageOneNameAction a s t pairing unions powers separation collection carrier maps
  let original : Fin 2 → (M.nameDomain s).names := ![cls Rc u, cls Rf w]
  let newPair : Fin 2 → (M.nameDomain s).names :=
    ![cls (moved h Rc) (moved h u), cls (moved h Rf) (moved h w)]
  let oldPair : Fin 2 → (M.nameDomain s).names :=
    ![cls (moved h Rc) oldU, cls (moved h Rf) oldW]
  dsimp only
  intro profiles bases coinitial functions supported decisions equalities newSupport oldSupport newHS oldHS single reference
  have above : E ≤ V := (d.iso h).le_iff_le.1 (overlap ▸ anchor)
  have indexEq := M.niceRefinementIndex_copies_agree a s b d level T T2 valid valid2
    indices C E U Rf Rc member g h V above relative
  have fields := (refinementIndexCode_eq_iff _ _ _ _ _ _ _ _ _ _ _ _).1 indexEq
  have fine : moved h Rf = moved g Rf := Subtype.ext (Subtype.ext fields.2.2.2.2.1)
  have coarse : moved h Rc = moved g Rc := Subtype.ext (Subtype.ext fields.2.2.2.2.2)
  have classLaw (k : G) (R v : (M.nameDomain s).names) :
      moved k (cls R v) = cls (moved k R) (moved k v) :=
    M.stageOneNameAction_class a s t pairing unions powers separation collection carrier maps
      order hT valid closed k R v
  have newLaw (i : Fin 2) : moved h (original i) = newPair i := by
    exact Fin.cases (classLaw h Rc u) (Fin.cases (classLaw h Rf w) (fun j => Fin.elim0 j)) i
  have shape (i : Fin 2) : (moved h (original i)).val.val ⊆ ZFSet.prod T s.carrier := by
    rw [newLaw]
    exact Fin.cases (Name.refinementClass_subset T valid (moved h Rc).val (moved h u).val)
      (Fin.cases (Name.refinementClass_subset T valid (moved h Rf).val (moved h w).val)
        (fun j => Fin.elim0 j)) i
  have transported := (M.stageOneProfile_act_iff a s t pairing unions powers separation collection
    carrier order maps hT valid closed b d base directed system h Rc Rf u w V p).2
    (single.2.1 V above)
  have profile : Forces (M.nameDomain s) refinementProfileFormula
      ![moved h (original 0), moved h (original 1),
        M.stageOneVisibilityName s valid a b d base directed system (d.iso h V)] q := by
    rw [newLaw 0, newLaw 1]
    exact forces_mono (M.nameDomain s) _ _ transported qh
  have referenceFormula : Forces (M.nameDomain s) refinementCollisionFormula
      ![moved g (original 0), oldPair 0, moved g (original 1), oldPair 1] q := by
    change Forces (M.nameDomain s) refinementCollisionFormula
      ![moved g (cls Rc u), cls (moved h Rc) oldU,
        moved g (cls Rf w), cls (moved h Rf) oldW] q
    rw [classLaw g Rc u, classLaw g Rf w, ← fine, ← coarse]
    exact reference
  have forced := M.prepared_joint_mixed_collision_forces a s t b d pairing unions powers separation collection
    carrier group nodes supports maps hT valid closed base directed system meet descent small F B f
    original oldPair p q profiles bases coinitial functions supported decisions equalities g h V A X
    relative qh qg overlap (fun i => (newLaw i).symm ▸ newSupport i) oldSupport
    (fun i => (newLaw i).symm ▸ newHS i) oldHS shape profile referenceFormula
  have typed : M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid
      (moved h Rf) (moved h Rc) (moved h u) oldU (moved h w) oldW q := by
    rw [newLaw 0, newLaw 1] at forced
    exact forced
  have movedMember := (M.niceRefinementIndex_act_iff a s t b d pairing unions powers separation collection
    carrier order maps level T T2 valid closed closed2 indices.family_ground h C E U Rf Rc).2 member
  refine ⟨typed, ?_⟩
  exact (M.refinementLevelRawCollision_iff a s b d level pairing unions powers separation collection
    carrier order hT valid indices (d.iso h C) (d.iso h E) (moved h U) (moved h Rf) (moved h Rc)
    (moved h u) oldU (moved h w) oldW movedMember q).2 typed

end TransitiveGround

namespace TransitiveGround
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
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (group : t.carrier ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
variable (closed : ∀ g (tau : Name s), tau.val ∈ T → (a.act s g tau).val ∈ T)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)
variable (meet : L → L → L)
variable (descent : ∀ (H : ConditionFilter P),
  H.GenericFor (M.codedFamily s) →
  H.GenericFor (formulaFamily (M.nameDomain s)) →
  ∀ (v w : L) (x y : (M.nameDomain s).names),
    d.principalFix v ≤ a.stabilizer s x.val →
    d.principalFix w ≤ a.stabilizer s y.val →
    HereditarilySymmetric a s (d.principalSupportFamily base directed) x.val →
    HereditarilySymmetric a s (d.principalSupportFamily base directed) y.val →
    Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
    ∃ tau : (M.nameDomain s).names,
      HereditarilySymmetric a s (d.principalSupportFamily base directed) tau.val ∧
      d.principalFix (meet v w) ≤ a.stabilizer s tau.val ∧
      Name.eval {p | H.mem p} tau.val = Name.eval {p | H.mem p} x.val)

variable {T2 : ZFSet.{u}} (valid2 : ∀ z ∈ T2, IsName s z)
variable (closed2 : ∀ g (tau : Name s), tau.val ∈ T2 → (a.act s g tau).val ∈ T2)
variable (level : ZFSet.{u})
variable (indices : NiceRefinementIndexSystem M a s b d level T T2 valid valid2)

include group nodes supports closed closed2 descent indices in
theorem prepared_joint_refinementCollision_of_position_supports (small : M.sets.Countable)
    (children : ∀ tau : Name s, tau.val ∈ T →
      HereditarilySymmetric a s (d.principalSupportFamily base directed) tau)
    (C E : L) (U Rf Rc u w oldU oldW : (M.nameDomain s).names)
    (member : refinementIndexCode level (b.encode C) (b.encode E)
      U.val.val Rf.val.val Rc.val.val ∈ M.niceRefinementIndices a s b d level T T2 valid)
    (F B f : Fin 2 → ZFSet.{u}) (p q : P) (g h : G) (V A X : L)
    (relative : g⁻¹ * h ∈ d.principalFix V)
    (qh : q ≤ a.iso h p) (qg : q ≤ a.iso g p)
    (overlap : meet A X = d.iso h V) (anchor : d.iso h E ≤ meet A X)
    (meetLeft : meet A X ≤ A) (meetRight : meet A X ≤ X) :
    let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
    let moved := M.stageOneNameAction a s t pairing unions powers separation collection carrier maps
    let original := ![cls Rc u, cls Rf w]
    ∀ (_profiles : ∀ i, F i ⊆ b.carrier) (_bases : ∀ i, B i ⊆ F i)
      (_coinitial : ∀ i, ∀ x ∈ F i, ∃ v ∈ B i, ZFSet.pair v x ∈ b.conditionOrder)
      (_functions : ∀ i, ZFSet.IsFunc (B i) (M.niceSupportNameCodes a s T d.principalFix) (f i))
      (_supported : ∀ i, f i ⊆ M.niceSupportRelation a s b T d.principalFix)
      (_decisions : ∀ i, M.DecidesVisibilityProfile a s b d.principalFix T (F i) (original i).val p)
      (_equalities : ∀ i, ∀ v ∈ B i, ∀ tau : Name s,
        tau.val ∈ M.niceSupportNameCodes a s T d.principalFix →
        ZFSet.pair v tau.val ∈ f i → Name.ForcesEq p (original i).val tau)
      (_newPositions : ∀ i : Fin 2, d.principalFix A ≤
        a.stabilizer s (![ (moved h u).val, (moved h w).val ] i))
      (_oldPositions : ∀ i : Fin 2, d.principalFix X ≤
        a.stabilizer s (![oldU.val, oldW.val] i))
      (_single : M.stageOneSingleTests s pairing unions powers separation collection carrier order hT valid
        a b d base directed system C E U Rf Rc u w p)
      (_reference : M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid
        (moved h Rf) (moved h Rc) (moved g u) oldU (moved g w) oldW q),
      M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid
        (moved h Rf) (moved h Rc) (moved h u) oldU (moved h w) oldW q ∧
      stageOneRawCollision M (M.refinementLevelFormulaData a s b d level T T2 valid)
        (refinementIndexCode level (b.encode (d.iso h C)) (b.encode (d.iso h E))
          (moved h U).val.val (moved h Rf).val.val (moved h Rc).val.val)
        (moved h u).val.val oldU.val.val (moved h w).val.val oldW.val.val (s.encode q) := by
  let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
  let moved := M.stageOneNameAction a s t pairing unions powers separation collection carrier maps
  let newPair : Fin 2 → (M.nameDomain s).names :=
    ![cls (moved h Rc) (moved h u), cls (moved h Rf) (moved h w)]
  let oldPair : Fin 2 → (M.nameDomain s).names :=
    ![cls (moved h Rc) oldU, cls (moved h Rf) oldW]
  dsimp only
  intro profiles bases coinitial functions supported decisions equalities newPositions oldPositions single reference
  have movedMember := (M.niceRefinementIndex_act_iff a s t b d pairing unions powers separation collection
    carrier order maps level T T2 valid closed closed2 indices.family_ground h C E U Rf Rc).2 member
  have newSupports := M.niceRefinementClasses_supported_by_block a s b d level T T2 valid valid2
    indices base directed closed children (d.iso h C) (d.iso h E) A
    (moved h U) (moved h Rf) (moved h Rc) movedMember (anchor.trans meetLeft)
    ![(moved h u).val, (moved h w).val] newPositions
  have oldSupports := M.niceRefinementClasses_supported_by_block a s b d level T T2 valid valid2
    indices base directed closed children (d.iso h C) (d.iso h E) X
    (moved h U) (moved h Rf) (moved h Rc) movedMember (anchor.trans meetRight)
    ![oldU.val, oldW.val] oldPositions
  have newFacts : ∀ i, d.principalFix A ≤ a.stabilizer s (newPair i).val ∧
      HereditarilySymmetric a s (d.principalSupportFamily base directed) (newPair i).val :=
    Fin.cases (newSupports 0) (Fin.cases (newSupports 1) (fun j => Fin.elim0 j))
  have oldFacts : ∀ i, d.principalFix X ≤ a.stabilizer s (oldPair i).val ∧
      HereditarilySymmetric a s (d.principalSupportFamily base directed) (oldPair i).val :=
    Fin.cases (oldSupports 0) (Fin.cases (oldSupports 1) (fun j => Fin.elim0 j))
  exact M.prepared_joint_refinementCollision_tests a s t b d pairing unions powers separation collection
    carrier order group nodes supports maps hT valid closed base directed system meet descent
    valid2 closed2 level indices small C E U Rf Rc u w oldU oldW member F B f p q g h V A X
    relative qh qg overlap anchor profiles bases coinitial functions supported decisions equalities
    (fun i => (newFacts i).1) (fun i => (oldFacts i).1)
    (fun i => (newFacts i).2) (fun i => (oldFacts i).2) single reference

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRecursiveRowNameActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization Compression.RecursiveMaps
universe u v
variable (M : TransitiveGround.{u}) {R : Type u} (c : Presentation R)
variable {T stages history : ZFSet.{u}}
variable (run : RecursiveRefinementDataHistory M c.carrier T stages history)
variable (ordinal : ordinalSetProperty stages) (carrier : c.carrier ∈ M.sets)
local notation "Q" => M.refinementHistoryForcing c.carrier T stages history
local notation "pres" => SetMembers.presentation Q
local notation "liftName" => M.refinementHistoryRowNameLift c run ordinal carrier
variable {G : Type v} [Group G] [PartialOrder R]
variable [PartialOrder (SetMembers (M.refinementHistoryForcing c.carrier T stages history))]
variable (a : PosetAction G R)
variable (e : PosetAction G (SetMembers (M.refinementHistoryForcing c.carrier T stages history)))
variable (image : G → ZFSet.{u} → ZFSet.{u})
variable (coordinates : ∀ (g : G)
  (q : SetMembers (M.refinementHistoryForcing c.carrier T stages history)) (row : R) (A : ZFSet.{u}),
  SetMembers.raw q = ZFSet.pair (c.encode row) A →
  SetMembers.raw (e.iso g q) = ZFSet.pair (c.encode (a.iso g row)) (image g A))
variable (emptyImage : ∀ g, image g ∅ = ∅)
include run ordinal carrier coordinates emptyImage

theorem refinementHistoryRowNameLift_stabilizer (tau : Name c.pairEmpty) :
    e.stabilizer (pres) (liftName tau) = a.stabilizer c.pairEmpty tau := by
  apply Subgroup.ext
  intro g
  change e.act (pres) g (liftName tau) = liftName tau ↔ a.act c.pairEmpty g tau = tau
  rw [M.refinementHistoryRowNameLift_act c run ordinal carrier a e image coordinates emptyImage]
  constructor
  · intro equal
    apply Subtype.ext
    have codes := congrArg Subtype.val equal
    simpa only [M.refinementHistoryRowNameLift_val c run ordinal carrier] using codes
  · intro equal
    exact congrArg liftName equal

end PartitionPilot.Forcing.TransitiveGround

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



namespace PartitionPilot.Forcing.TransitiveGround
universe u
variable (M : TransitiveGround.{u})
variable (G nodes nodeOrder nodeAction basis T T2 : ZFSet.{u})
variable {stages history level P order top action : ZFSet.{u}}
variable (function : FunctionGraphOn stages history)
variable (stored : ZFSet.pair level (forcingStageCode P order top action) ∈ history)
include function stored

theorem structuralAssignmentActionGraph_branch_iff {g x y : ZFSet.{u}}
    (edge : ZFSet.pair (ZFSet.pair g x) y ∈
      M.structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2 stages history) :
    x ∈ stageOneAssignments
      (M.rawRefinementFormulaData P order top action G nodes nodeOrder basis T T2 level 0) T ↔
    y ∈ stageOneAssignments
      (M.rawRefinementFormulaData P order top action G nodes nodeOrder basis T T2 level 0) T := by
  constructor
  · intro member
    have branch := (M.structuralAssignmentActionGraph_branch_entry G nodes nodeOrder basis T T2
      nodeAction function stored member g y).1 edge |>.2
    exact (ZFSet.pair_mem_prod.1 (M.rawStageRefinementAssignmentActionGraph_branch_bound
      g P order top action G nodes nodeOrder nodeAction basis T T2 level branch)).2
  · intro member
    obtain ⟨_, other, _, P', order', top', action', stored', branch⟩ :=
      (M.pair_mem_structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2
        stages history g x y).1 edge
    have bounds := ZFSet.pair_mem_prod.1
      (M.rawStageRefinementAssignmentActionGraph_branch_bound g P' order' top' action'
        G nodes nodeOrder nodeAction basis T T2 other branch)
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := M.structuralAssignment_branch_unique
      G nodes nodeOrder basis T T2 function stored stored' member bounds.2
    exact bounds.1

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

theorem structuralAssignmentImage_decode
    {stages history : ZFSet.{u}} (function : FunctionGraphOn stages history)
    (stored : ZFSet.pair level (forcingStageCode s.carrier s.conditionOrder (s.encode ⊤)
      (a.actionGraph s t)) ∈ history)
    (h : G) (A sharedIdx rawU rawW : ZFSet.{u})
    (index : sharedIdx ∈ M.niceRefinementIndices a s b d level T T2 system.valid1)
    (hu : rawU ∈ T) (hw : rawW ∈ T)
    (member : stageOneAssignment sharedIdx rawU rawW ∈
      M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 stages history (t.encode h) A) :
    ∃ (C E : L) (U Rf Rc u w : (M.nameDomain s).names),
      refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
        M.niceRefinementIndices a s b d level T T2 system.valid1 ∧
      u.val.val ∈ T ∧ w.val.val ∈ T ∧
      stageOneAssignment
        (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
        u.val.val w.val.val ∈ A ∧
      sharedIdx = refinementIndexCode level (b.encode (d.iso h C)) (b.encode (d.iso h E))
        (a.act s h U.val).val (a.act s h Rf.val).val (a.act s h Rc.val).val ∧
      rawU = (a.act s h u.val).val ∧ rawW = (a.act s h w.val).val ∧
      ZFSet.pair (ZFSet.pair (t.encode h) (stageOneAssignment
        (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
        u.val.val w.val.val)) (stageOneAssignment sharedIdx rawU rawW) ∈
        M.structuralAssignmentActionGraph t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
          (supportBasisCode b t d.principalFix) T T2 stages history := by
  obtain ⟨x, source, edge⟩ := (M.structuralAssignmentImage_entry t.carrier b.carrier b.conditionOrder
    (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 stages history
    (t.encode h) A _).1 member
  have dataEq := M.rawRefinementFormulaData_eq a s t b d pairing unions powers separation collection
    carrier group nodes supports system.inputs.condition_maps level T T2 system.valid1 system.valid2
  have target : stageOneAssignment sharedIdx rawU rawW ∈ stageOneAssignments
      (M.rawRefinementFormulaData s.carrier s.conditionOrder (s.encode ⊤) (a.actionGraph s t)
        t.carrier b.carrier b.conditionOrder (supportBasisCode b t d.principalFix) T T2 level 0) T := by
    rw [dataEq]
    exact (stageOneAssignment_mem_assignments _ _ _ _ _).2 ⟨index, hu, hw⟩
  have branchMember := (M.structuralAssignmentActionGraph_branch_iff t.carrier b.carrier
    b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2
    function stored edge).2 target
  have original := branchMember
  rw [dataEq] at original
  obtain ⟨idx, hi, originalU, hOriginalU, originalW, hOriginalW, rfl⟩ :=
    (mem_stageOneAssignments _ _ x).1 original
  obtain ⟨C, E, U, Rf, Rc, rfl⟩ :=
    M.exists_niceRefinementIndex_fields a s b d level T T2 system.valid1 system.valid2 hi
  let u : (M.nameDomain s).names :=
    ⟨⟨originalU, system.valid1 originalU hOriginalU⟩, M.transitive hT hOriginalU⟩
  let w : (M.nameDomain s).names :=
    ⟨⟨originalW, system.valid1 originalW hOriginalW⟩, M.transitive hT hOriginalW⟩
  have branch := ((M.structuralAssignmentActionGraph_branch_entry t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 (d.actionGraph b t) function stored
    branchMember (t.encode h) (stageOneAssignment sharedIdx rawU rawW)).1 edge).2
  rw [M.rawStageRefinementAssignmentActionGraph_eq a s t b d pairing unions powers separation collection
    carrier group nodes order system.inputs.condition_maps system.inputs.node_maps supports level T T2
    hLevel hT system.valid1 system.valid2 system.inputs.terms_closed system.inputs.pairs_closed
    system.inputs.family_ground system.indices.index_ground h] at branch
  have moved := (M.refinementAssignmentActionGraph_entry a s b d level T T2 system.valid1
    system.valid2 system.inputs.terms_closed t pairing unions powers separation collection carrier
    order system.inputs.condition_maps system.inputs.pairs_closed system.inputs.family_ground
    h C E U Rf Rc u.val w.val hi hOriginalU hOriginalW _).1 branch
  obtain ⟨sameIndex, sameU, sameW⟩ := (stageOneAssignment_eq_iff _ _ _ _ _ _).1 moved
  exact ⟨C, E, U, Rf, Rc, u, w, hi, hOriginalU, hOriginalW, source,
    sameIndex, sameU, sameW, edge⟩

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundStageTwoNamePositionSupports
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace PosetAction
open SetRealization
universe u
variable {G P Q L : Type u} [Group G] [PartialOrder P] [PartialOrder Q] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (e : PosetAction G Q) (t : Presentation Q)
variable (liftName : Name s → Name t)
variable (codes : ∀ τ, (liftName τ).val = τ.val)
variable (stabilizers : ∀ τ, e.stabilizer t (liftName τ) = a.stabilizer s τ)
include codes stabilizers

theorem positionSupport_of_codeLift (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (b : Presentation L) (d : PosetAction G L) (S mu X tuples : ZFSet.{u}) (D : L)
    (range : ∀ f z, ZFSet.pair f z ∈ tuples → z ∈ T)
    (support : ∀ f ∈ S, ∀ τ : Name s, ZFSet.pair f τ.val ∈ tuples →
      RowPositionBound mu X b.conditionOrder f (b.encode D) →
      d.principalFix D ≤ a.stabilizer s τ) :
    ∀ f ∈ S, ∀ τ : Name t, ZFSet.pair f τ.val ∈ tuples →
      RowPositionBound mu X b.conditionOrder f (b.encode D) →
      d.principalFix D ≤ e.stabilizer t τ := by
  intro f hf τ entry bound
  let lower : Name s := ⟨τ.val, valid τ.val (range f τ.val entry)⟩
  have same : liftName lower = τ := Subtype.ext (codes lower)
  rw [← same, stabilizers]
  exact support f hf lower entry bound

end PosetAction

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticAssignmentLabelDomainTotality
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

theorem semanticStructuralPrefix_stageSystem :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation Q
    RefinementStageSystem M act lower t b d base directed alpha T T2 := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hLowerPacked := M.graphRestriction_mem unions separation hAlpha hPacked
  have hGraph : (act).actionGraph lower t ∈ M.sets := by
    rw [M.semanticStructuralPrefixAction_graph]
    have ground := M.structuralForcingActionGraph_mem pairing unions powers separation collection
      carrier rowAction group nodes nodeOrder nodeAction supports hT hT2 hAlpha hh omega
    unfold structuralForcingCarrier at ground
    rw [M.structuralRefinementHistory_domain_restrict t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 subset] at ground
    exact ground
  let image := fun g A => M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder
    (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 alpha history (t.encode g) A
  have coordinates := M.semanticStructuralPrefixAction_coordinates c a t b d base directed
    T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction
    group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1
    closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset
  have emptyImage : ∀ g, image g ∅ = ∅ := fun g =>
    M.structuralAssignmentImage_empty t b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 alpha history (t.encode g)
  exact M.recursiveRefinementStageSystem c a t b d base directed T T2 alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal pairing unions powers separation collection
    carrier rowOrderGround group nodes nodeOrder nodeMaps supports hT hT2 hAlpha hLowerPacked
    omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 rowTop topMem topRows
    act image coordinates emptyImage hGraph

theorem semanticStructuralPrefix_assignmentImage_decode :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation Q
    let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    let fields := M.refinementLevelFormulaData act lower b d alpha T T2 valid
    ∀ (h : G) (A sharedIdx rawU rawW : ZFSet.{u}), sharedIdx ∈ fields 0 →
      rawU ∈ T → rawW ∈ T →
      stageOneAssignment sharedIdx rawU rawW ∈
        M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
          (supportBasisCode b t d.principalFix) T T2 stages history (t.encode h) A →
    ∃ (C E : L) (U Rf Rc u w : (M.nameDomain lower).names),
      refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈ fields 0 ∧
      u.val.val ∈ T ∧ w.val.val ∈ T ∧
      stageOneAssignment
        (refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
        u.val.val w.val.val ∈ A ∧
      sharedIdx = refinementIndexCode alpha (b.encode (d.iso h C)) (b.encode (d.iso h E))
        ((act).act lower h U.val).val ((act).act lower h Rf.val).val ((act).act lower h Rc.val).val ∧
      rawU = ((act).act lower h u.val).val ∧ rawW = ((act).act lower h w.val).val ∧
      ZFSet.pair (ZFSet.pair (t.encode h) (stageOneAssignment
        (refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
        u.val.val w.val.val)) (stageOneAssignment sharedIdx rawU rawW) ∈
        M.structuralAssignmentActionGraph t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
          (supportBasisCode b t d.principalFix) T T2 stages history := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  let fields := M.refinementLevelFormulaData act lower b d alpha T T2 valid
  have system := M.semanticStructuralPrefix_stageSystem c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hQ : lower.carrier ∈ M.sets := M.refinementHistoryForcing_mem pairing unions powers separation
    carrier hT hAlpha (M.graphRestriction_mem unions separation hAlpha hPacked) omega
  have orderGround : lower.conditionOrder ∈ M.sets := by
    rw [M.refinementHistoryDecodedOrder_eq]
    exact M.refinementHistoryOrder_mem pairing unions powers separation carrier rowOrderGround
      hT hAlpha (M.graphRestriction_mem unions separation hAlpha hPacked) omega
  obtain ⟨stage, stored⟩ := trace.1.total member
  have same := (trace.2 alpha member stage stored).trans
    (M.semanticStructuralPrefix_stageCode c a t b d base directed T T2 rowTop pairing unions powers
      separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps
      supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows
      hh ordinal trace hAlpha cutOrdinal subset)
  have exactStored : ZFSet.pair alpha
      (forcingStageCode lower.carrier lower.conditionOrder (lower.encode ⊤) ((act).actionGraph lower t))
      ∈ history := same ▸ stored
  dsimp only
  intro h A sharedIdx rawU rawW index hu hw imageMember
  exact M.structuralAssignmentImage_decode act lower t b d base directed alpha T T2 system
    pairing unions powers separation collection hQ orderGround group nodes supports hAlpha hT
    trace.1 exactStored h A sharedIdx rawU rawW index hu hw imageMember

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




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u

private theorem anchor_of_dataBound_p0 {L : Type u} [PartialOrder L]
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

theorem structuralAssignment_aligned_reference
    {stages history : ZFSet.{u}} (function : FunctionGraphOn stages history)
    (stored : ZFSet.pair level (forcingStageCode s.carrier s.conditionOrder (s.encode ⊤)
      (a.actionGraph s t)) ∈ history)
    (I S mu positions tuples sourceA newA oldA : ZFSet.{u})
    (g h : G) (D X V C E : L) (U Rf Rc : (M.nameDomain s).names) (u w : Name s)
    (index : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d level T T2 system.valid1)
    (hu : u.val ∈ T) (hw : w.val ∈ T)
    (source : stageOneAssignment
      (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
      u.val w.val ∈ sourceA)
    (i newU newW oldU oldW : ZFSet.{u})
    (edge : ZFSet.pair (ZFSet.pair (t.encode h) (stageOneAssignment
      (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val) u.val w.val))
      (stageOneAssignment i newU newW) ∈
      M.structuralAssignmentActionGraph t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 stages history)
    (newBound : ZFSet.pair (stageOneAssignment i newU newW) (b.encode (d.iso h D)) ∈
      stageOneDataBounds newA I T S b.carrier mu positions b.conditionOrder
        (refinementIndexFieldGraph I b.carrier 2) tuples)
    (oldBound : ZFSet.pair (stageOneAssignment i oldU oldW) (b.encode X) ∈
      stageOneDataBounds oldA I T S b.carrier mu positions b.conditionOrder
        (refinementIndexFieldGraph I b.carrier 2) tuples)
    (overlap : ∀ x : L, x ≤ d.iso h D → x ≤ X → x ≤ d.iso h V)
    (relative : g⁻¹ * h ∈ d.principalFix V)
    (contains : M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 stages history (t.encode g) sourceA ⊆ oldA) :
    d.iso h E ≤ d.iso h V ∧ E ≤ V ∧
    i = refinementIndexCode level (b.encode (d.iso h C)) (b.encode (d.iso h E))
      (a.act s h U.val).val (a.act s h Rf.val).val (a.act s h Rc.val).val ∧
    i = refinementIndexCode level (b.encode (d.iso g C)) (b.encode (d.iso g E))
      (a.act s g U.val).val (a.act s g Rf.val).val (a.act s g Rc.val).val ∧
    ZFSet.pair (ZFSet.pair (t.encode g) (stageOneAssignment
      (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val) u.val w.val))
      (stageOneAssignment i (a.act s g u).val (a.act s g w).val) ∈
      M.structuralAssignmentActionGraph t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 stages history ∧
    stageOneAssignment i (a.act s g u).val (a.act s g w).val ∈ oldA := by
  let z := stageOneAssignment
    (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val) u.val w.val
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
  have branch := ((M.structuralAssignmentActionGraph_branch_entry t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 (d.actionGraph b t) function stored
    branchMember (t.encode h) (stageOneAssignment i newU newW)).1 edge).2
  rw [graphEq h] at branch
  have moved := (M.refinementAssignmentActionGraph_entry a s b d level T T2 system.valid1
    system.valid2 system.inputs.terms_closed t pairing unions powers separation collection carrier
    order system.inputs.condition_maps system.inputs.pairs_closed system.inputs.family_ground
    h C E U Rf Rc u w index hu hw _).1 branch
  obtain ⟨indexH, termU, termW⟩ := (stageOneAssignment_eq_iff _ _ _ _ _ _).1 moved
  have hBelow := anchor_of_dataBound_p0 b I level T S mu positions tuples newA
    (d.iso h C) (d.iso h E) (d.iso h D)
    (a.act s h U.val).val (a.act s h Rf.val).val (a.act s h Rc.val).val
    newU newW (indexH ▸ newBound)
  have xBelow := anchor_of_dataBound_p0 b I level T S mu positions tuples oldA
    (d.iso h C) (d.iso h E) X
    (a.act s h U.val).val (a.act s h Rf.val).val (a.act s h Rc.val).val
    oldU oldW (indexH ▸ oldBound)
  have overlapAnchor := overlap (d.iso h E) hBelow xBelow
  have anchor : E ≤ V := (d.iso h).le_iff_le.mp overlapAnchor
  obtain ⟨strict, domain, fine, coarse, _validity⟩ :=
    (M.niceRefinementIndex_mem_iff a s b d pairing unions powers separation collection
      carrier order level T T2 system.valid1 system.inputs.family_ground C E U Rf Rc).1 index
  have nodeAgree (x : L) (below : x ≤ V) : d.iso h x = d.iso g x := by
    have fixed := relative x below
    calc
      d.iso h x = d.iso g (d.iso (g⁻¹ * h) x) := by rw [← d.mul]; simp only [mul_inv_cancel_left]
      _ = d.iso g x := congrArg (d.iso g) fixed
  have atC : g⁻¹ * h ∈ d.principalFix C := d.principalFix_antitone (strict.le.trans anchor) relative
  have nameAgree {K : ZFSet.{u}} (tau : Name s)
      (candidate : tau.val ∈ M.niceNameCandidates a s K (d.principalFix C)) :
      a.act s h tau = a.act s g tau := by
    obtain ⟨_ground, sigma, equal, _subset, support⟩ :=
      (M.mem_niceNameCandidates a s K (d.principalFix C) tau.val).1 candidate
    have same : sigma = tau := Subtype.ext equal
    subst sigma
    have fixed : a.act s (g⁻¹ * h) tau = tau := support atC
    calc
      a.act s h tau = a.act s g (a.act s (g⁻¹ * h) tau) := by
        rw [← a.act_mul]; simp only [mul_inv_cancel_left]
      _ = a.act s g tau := congrArg (a.act s g) fixed
  have indexG : i = refinementIndexCode level (b.encode (d.iso g C)) (b.encode (d.iso g E))
      (a.act s g U.val).val (a.act s g Rf.val).val (a.act s g Rc.val).val := by
    rw [indexH, nodeAgree C (strict.le.trans anchor), nodeAgree E anchor,
      nameAgree U.val domain, nameAgree Rf.val fine, nameAgree Rc.val coarse]
  have referenceBranch := (M.refinementAssignmentActionGraph_entry a s b d level T T2 system.valid1
    system.valid2 system.inputs.terms_closed t pairing unions powers separation collection carrier
    order system.inputs.condition_maps system.inputs.pairs_closed system.inputs.family_ground
    g C E U Rf Rc u w index hu hw (stageOneAssignment i (a.act s g u).val (a.act s g w).val)).2
      (congrArg (fun idx => stageOneAssignment idx (a.act s g u).val (a.act s g w).val) indexG)
  rw [← graphEq g] at referenceBranch
  have referenceEdge := (M.structuralAssignmentActionGraph_branch_entry t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 (d.actionGraph b t) function stored
    branchMember (t.encode g) (stageOneAssignment i (a.act s g u).val (a.act s g w).val)).2
      ⟨t.encode_mem g, referenceBranch⟩
  exact ⟨overlapAnchor, anchor, indexH, indexG, referenceEdge, contains
    ((M.structuralAssignmentImage_entry t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 stages history (t.encode g) sourceA _).2
      ⟨z, source, referenceEdge⟩)⟩

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

variable (meet : L → L → L)
variable (descent : ∀ (H : ConditionFilter P),
  H.GenericFor (M.codedFamily s) →
  H.GenericFor (formulaFamily (M.nameDomain s)) →
  ∀ (v w : L) (x y : (M.nameDomain s).names),
    d.principalFix v ≤ a.stabilizer s x.val →
    d.principalFix w ≤ a.stabilizer s y.val →
    HereditarilySymmetric a s (d.principalSupportFamily base directed) x.val →
    HereditarilySymmetric a s (d.principalSupportFamily base directed) y.val →
    Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
    ∃ tau : (M.nameDomain s).names,
      HereditarilySymmetric a s (d.principalSupportFamily base directed) tau.val ∧
      d.principalFix (meet v w) ≤ a.stabilizer s tau.val ∧
      Name.eval {p | H.mem p} tau.val = Name.eval {p | H.mem p} x.val)

include descent in
theorem structuralAssignment_prepared_aligned_collision
    (small : M.sets.Countable)
    {stages history : ZFSet.{u}} (function : FunctionGraphOn stages history)
    (stored : ZFSet.pair level (forcingStageCode s.carrier s.conditionOrder (s.encode ⊤)
      (a.actionGraph s t)) ∈ history)
    (I S mu positions tuples sourceA newA oldA : ZFSet.{u})
    (positionSupport : ∀ (D : L), ∀ f ∈ S, ∀ u : Name s, ZFSet.pair f u.val ∈ tuples →
      RowPositionBound mu positions b.conditionOrder f (b.encode D) →
      d.principalFix D ≤ a.stabilizer s u)
    (g h : G) (D X V C E : L) (U Rf Rc u w oldU oldW : (M.nameDomain s).names)
    (index : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d level T T2 system.valid1)
    (hu : u.val.val ∈ T) (hw : w.val.val ∈ T)
    (hOldU : oldU.val.val ∈ T) (hOldW : oldW.val.val ∈ T)
    (p q : P) (qh : q ≤ a.iso h p) (qg : q ≤ a.iso g p)
    (relative : g⁻¹ * h ∈ d.principalFix V)
    (overlap : meet (d.iso h D) X = d.iso h V)
    (meetLeft : meet (d.iso h D) X ≤ d.iso h D)
    (meetRight : meet (d.iso h D) X ≤ X)
    (meetGreatest : ∀ z : L, z ≤ d.iso h D → z ≤ X → z ≤ meet (d.iso h D) X)
    (F B f e names : Fin 2 → ZFSet.{u}) :
    let fields := M.refinementLevelFormulaData a s b d level T T2 system.valid1
    let moved := M.stageOneNameAction a s t pairing unions powers separation collection carrier system.inputs.condition_maps
    let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT system.valid1
    let idx := refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
    let movedIdx := refinementIndexCode level (b.encode (d.iso h C)) (b.encode (d.iso h E))
      (moved h U).val.val (moved h Rf).val.val (moved h Rc).val.val
    stageOneAssignment idx u.val.val w.val.val ∈ sourceA →
    ZFSet.pair (ZFSet.pair (t.encode h) (stageOneAssignment idx u.val.val w.val.val))
      (stageOneAssignment movedIdx (moved h u).val.val (moved h w).val.val) ∈
      M.structuralAssignmentActionGraph t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 stages history →
    ZFSet.pair (stageOneAssignment movedIdx (moved h u).val.val (moved h w).val.val)
      (b.encode (d.iso h D)) ∈ stageOneDataBounds newA I T S b.carrier mu positions b.conditionOrder
        (refinementIndexFieldGraph I b.carrier 2) tuples →
    ZFSet.pair (stageOneAssignment movedIdx oldU.val.val oldW.val.val) (b.encode X) ∈
      stageOneDataBounds oldA I T S b.carrier mu positions b.conditionOrder
        (refinementIndexFieldGraph I b.carrier 2) tuples →
    M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 stages history (t.encode g) sourceA ⊆ oldA →
    stageOneRawTests M fields sourceA (s.encode p) → stageOneRawTests M fields oldA (s.encode q) →
    (∀ i : Fin 2, PreparedCertificateCode M s.carrier s.conditionOrder (s.encode p)
      b.carrier b.conditionOrder (canonicalMeetGraph b.carrier b.conditionOrder)
      (M.groundRelations T s.carrier) (M.niceVisibilityGraph a s b T d.principalFix) (s.encode ⊤)
      ZFSet.omega ((![cls Rc u, cls Rf w] : Fin 2 → (M.nameDomain s).names) i).val.val
      (F i) (B i) (f i) (e i) (names i)) →
    stageOneRawCollision M fields movedIdx (moved h u).val.val oldU.val.val
      (moved h w).val.val oldW.val.val (s.encode q) ∧
    stageOneRawCollision M fields movedIdx oldU.val.val (moved h u).val.val
      oldW.val.val (moved h w).val.val (s.encode q) := by
  let fields := M.refinementLevelFormulaData a s b d level T T2 system.valid1
  let moved := M.stageOneNameAction a s t pairing unions powers separation collection carrier system.inputs.condition_maps
  let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT system.valid1
  let idx := refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
  let movedIdx := refinementIndexCode level (b.encode (d.iso h C)) (b.encode (d.iso h E))
    (moved h U).val.val (moved h Rf).val.val (moved h Rc).val.val
  dsimp only
  intro source edge newBound oldBound contains sourceTests oldTests certificates
  have aligned := M.structuralAssignment_aligned_reference a s t b d base directed level T T2 system
    pairing unions powers separation collection carrier order group nodes supports hLevel hT function stored
    I S mu positions tuples sourceA newA oldA g h D X V C E U Rf Rc u.val w.val index hu hw source
    movedIdx (moved h u).val.val (moved h w).val.val oldU.val.val oldW.val.val edge newBound oldBound
    (fun z hz hx => overlap ▸ meetGreatest z hz hx) relative contains
  have anchor : d.iso h E ≤ meet (d.iso h D) X := overlap.symm ▸ aligned.1
  have movedMember := (M.niceRefinementIndex_act_iff a s t b d pairing unions powers separation collection
    carrier order system.inputs.condition_maps level T T2 system.valid1 system.inputs.terms_closed
    system.inputs.pairs_closed system.inputs.family_ground h C E U Rf Rc).2 index
  have oldMember : stageOneAssignment movedIdx oldU.val.val oldW.val.val ∈ oldA :=
    (stageOneDataBounds_assignment_entry oldA I T S b.carrier mu positions b.conditionOrder
      (refinementIndexFieldGraph I b.carrier 2) tuples movedIdx oldU.val.val oldW.val.val (b.encode X)).1 oldBound |>.1
  have referenceRaw := oldTests.2 movedIdx movedMember
    (moved g u).val.val (system.inputs.terms_closed g u.val hu) oldU.val.val hOldU
    (moved g w).val.val (system.inputs.terms_closed g w.val hw) oldW.val.val hOldW
    aligned.2.2.2.2.2 oldMember
  have reference := (M.refinementLevelRawCollision_iff a s b d level pairing unions powers separation collection
    carrier order hT system.valid1 system.indices (d.iso h C) (d.iso h E)
    (moved h U) (moved h Rf) (moved h Rc) (moved g u) oldU (moved g w) oldW movedMember q).1 referenceRaw
  have single := (M.refinementLevelRawSingle_iff a s b d level pairing unions powers separation collection
    carrier order nodes hT system.valid1 system.indices base directed system.first C E U Rf Rc u w index p).1
    (sourceTests.1 idx index u.val.val hu w.val.val hw source)
  have positionsOfBound (A : ZFSet.{u}) (Z : L) (v v' : Name s)
      (bound : ZFSet.pair (stageOneAssignment movedIdx v.val v'.val) (b.encode Z) ∈
        stageOneDataBounds A I T S b.carrier mu positions b.conditionOrder
          (refinementIndexFieldGraph I b.carrier 2) tuples) :
      d.principalFix Z ≤ a.stabilizer s v ∧ d.principalFix Z ≤ a.stabilizer s v' := by
    obtain ⟨_, _, _, _, _, rawE, _, fu, hfu, fw, hfw, _anchor, _below, tu, tw, bu, bw⟩ :=
      (stageOneDataBounds_assignment_entry A I T S b.carrier mu positions b.conditionOrder
        (refinementIndexFieldGraph I b.carrier 2) tuples movedIdx v.val v'.val (b.encode Z)).1 bound
    exact ⟨positionSupport Z fu hfu v tu bu, positionSupport Z fw hfw v' tw bw⟩
  have newPositions := positionsOfBound newA (d.iso h D) (moved h u).val (moved h w).val newBound
  have oldPositions := positionsOfBound oldA X oldU.val oldW.val oldBound
  have recognized (i : Fin 2) := M.preparedCertificateCode_typed a s b T d.principalFix pairing unions powers
    separation collection carrier order hT system.valid1 system.first.visibility_graph_ground
    b.conditionOrder (canonicalMeetGraph b.carrier b.conditionOrder) ZFSet.omega
    ((![cls Rc u, cls Rf w] : Fin 2 → (M.nameDomain s).names) i) p
    (F i) (B i) (f i) (e i) (names i) (certificates i)
  have collision := M.prepared_joint_refinementCollision_of_position_supports a s t b d
    pairing unions powers separation collection carrier order group nodes supports system.inputs.condition_maps
    hT system.valid1 system.inputs.terms_closed base directed system.first meet descent
    system.valid2 system.inputs.pairs_closed level system.indices small system.terms_hs
    C E U Rf Rc u w oldU oldW index F B f p q g h V (d.iso h D) X relative qh qg overlap anchor
    meetLeft meetRight
    (fun i => (recognized i).1.subset) (fun i => (recognized i).2.1.1)
    (fun i => (recognized i).2.1.2) (fun i => (recognized i).2.2.2.1.1)
    (fun i => (recognized i).2.2.2.2.1) (fun i => (recognized i).2.2.2.2.2.1)
    (fun i => (recognized i).2.2.2.2.2.2)
    (Fin.cases newPositions.1 (Fin.cases newPositions.2 (fun j => Fin.elim0 j)))
    (Fin.cases oldPositions.1 (Fin.cases oldPositions.2 (fun j => Fin.elim0 j))) single reference
  exact M.refinementLevelRawCollision_both_orders s pairing unions powers separation collection carrier order
    hT system.valid1 a b d level T2 system.indices (d.iso h C) (d.iso h E)
    (moved h U) (moved h Rf) (moved h Rc) (moved h u) oldU (moved h w) oldW movedMember q collision.1

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticAlignedCopyCollisions
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

theorem semanticStructuralPrefix_preparationEnvironment (fields : Fin 15 → ZFSet.{u})
    (stored : ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed) :
    StoredPreparationEnvironment M fields := by
  let instLowerHistoryOrder := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let instLowerHistoryTop := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  have exactStored := M.semanticStructuralPrefix_refinementData_entry c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  have same : fields = M.refinementLevelFormulaData act lower b d alpha T T2 valid :=
    refinementFormulaDataCode_injective ((run).carriers.data.function.unique stored exactStored)
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have members : ∀ j, fields j ∈ M.sets := M.refinementFormulaDataCode_fields_mem fields
    (M.transitive (M.union_mem unions (M.union_mem unions hPacked)) (pair_second_mem_doubleUnion stored))
  refine ⟨?_, members, ?_, ?_⟩
  · rw [same]
    exact lower.conditionOrder_code
  · rw [same]
    intro z hz
    exact Name.isName_of_subset valid ((M.mem_groundRelations T lower.carrier z).1 hz).2
  · rw [same]
    intro v V entry _
    obtain ⟨i, equal⟩ := (M.mem_niceVisibilityGraph act lower b T d.principalFix
      (ZFSet.pair v V)).1 entry
    have value := (ZFSet.pair_inj.1 equal).2
    rw [value]
    exact (M.niceVisibilityName act lower T (d.principalFix i)).property

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticAlignedRectangleUnions
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

local notation "upperQ" => M.refinementHistoryForcing c.carrier T stages packed
local notation "levels" => refinementDataHistoryLevels stages packed T
local notation "image" => M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder
  (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 stages history

theorem semanticStructuralPrefix_aligned_copy_crossCollisions_at_larger_cut_oai
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable) (meet : L → L → L)
    (I S mu positions tuples : ZFSet.{u})
    (range : ∀ f z, ZFSet.pair f z ∈ tuples → z ∈ T)
    (support : ∀ (D : L), ∀ f ∈ S, ∀ u : Name c.pairEmpty, ZFSet.pair f u.val ∈ tuples →
      RowPositionBound mu positions b.conditionOrder f (b.encode D) →
      d.principalFix D ≤ a.stabilizer c.pairEmpty u)
    (r oldRow row : R) (A oldA largerA : ZFSet.{u}) (g h : G) (D X V : L)
    (source : ZFSet.pair (c.encode r) A ∈ upperQ)
    (oldSource : ZFSet.pair (c.encode oldRow) oldA ∈ upperQ)
    (prepared : StoredPreparedConditionCode M c.carrier T stages packed b.carrier (ZFSet.pair (c.encode r) A))
    (belowOld : row ≤ oldRow) (oldBelowG : oldRow ≤ a.iso g r) (belowH : row ≤ a.iso h r)
    (contains : image (t.encode g) A ⊆ oldA)
    (movedSubset : image (t.encode h) A ⊆ largerA)
    (oldSubset : oldA ⊆ largerA)
    (relative : g⁻¹ * h ∈ d.principalFix V)
    (overlap : meet (d.iso h D) X = d.iso h V)
    (meetLeft : meet (d.iso h D) X ≤ d.iso h D)
    (meetRight : meet (d.iso h D) X ≤ X)
    (meetGreatest : ∀ z : L, z ≤ d.iso h D → z ≤ X → z ≤ meet (d.iso h D) X) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation Q
    let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    let fields := M.refinementLevelFormulaData act lower b d alpha T T2 valid
    ∀ (_descent : ∀ (H : ConditionFilter (SetMembers Q)),
      H.GenericFor (M.codedFamily lower) → H.GenericFor (formulaFamily (M.nameDomain lower)) →
      ∀ (v w : L) (x y : (M.nameDomain lower).names),
        d.principalFix v ≤ (act).stabilizer lower x.val →
        d.principalFix w ≤ (act).stabilizer lower y.val →
        HereditarilySymmetric act lower (d.principalSupportFamily base directed) x.val →
        HereditarilySymmetric act lower (d.principalSupportFamily base directed) y.val →
        Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
        ∃ tau : (M.nameDomain lower).names,
          HereditarilySymmetric act lower (d.principalSupportFamily base directed) tau.val ∧
          d.principalFix (meet v w) ≤ (act).stabilizer lower tau.val ∧
          Name.eval {p | H.mem p} tau.val = Name.eval {p | H.mem p} x.val),
      (∀ z ∈ image (t.encode h) A, ZFSet.pair z (b.encode (d.iso h D)) ∈
        stageOneDataBounds (image (t.encode h) A) I T S b.carrier mu positions b.conditionOrder
          (refinementIndexFieldGraph I b.carrier 2) tuples) →
      (∀ z ∈ oldA, ZFSet.pair z (b.encode X) ∈
        stageOneDataBounds oldA I T S b.carrier mu positions b.conditionOrder
          (refinementIndexFieldGraph I b.carrier 2) tuples) →
      ZFSet.pair (c.encode row) (assignmentCut levels alpha largerA) ∈ Q →
      stageOneRawCrossCollisions M fields (image (t.encode h) A) oldA
        (ZFSet.pair (c.encode row) (assignmentCut levels alpha largerA)) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  let fields := M.refinementLevelFormulaData act lower b d alpha T T2 valid
  dsimp only
  intro descent newData oldData validCut
  have system := M.semanticStructuralPrefix_stageSystem c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  have canonicalStored := M.semanticStructuralPrefix_refinementData_entry c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  have environment := M.semanticStructuralPrefix_preparationEnvironment c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member fields canonicalStored
  have hQ : lower.carrier ∈ M.sets := environment.ground 7
  have orderGround : lower.conditionOrder ∈ M.sets := environment.ground 8
  obtain ⟨stage, stored⟩ := trace.1.total member
  have sameStage := (trace.2 alpha member stage stored).trans
    (M.semanticStructuralPrefix_stageCode c a t b d base directed T T2 rowTop pairing unions powers
      separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps
      supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows
      hh ordinal trace hAlpha cutOrdinal subset)
  have exactStored : ZFSet.pair alpha
      (forcingStageCode lower.carrier lower.conditionOrder (lower.encode ⊤) ((act).actionGraph lower t))
      ∈ history := sameStage ▸ stored
  let localImage := fun g A => M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder
    (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 alpha history (t.encode g) A
  have coordinates := M.semanticStructuralPrefixAction_coordinates c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hh trace hAlpha cutOrdinal subset
  have emptyImage : ∀ g, localImage g ∅ = ∅ := fun g =>
    M.structuralAssignmentImage_empty t b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 alpha history (t.encode g)
  have liftedSupport (Z : L) := a.positionSupport_of_codeLift c.pairEmpty act lower
    (M.refinementHistoryRowNameLift c ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier)
    (M.refinementHistoryRowNameLift_val c ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier)
    (M.refinementHistoryRowNameLift_stabilizer c ((run).carriers.restrict cutOrdinal subset) cutOrdinal
      carrier a act localImage coordinates emptyImage)
    T valid1 b d S mu positions tuples Z range (support Z)
  let qStrong : SetMembers Q := SetMembers.ofMem _ validCut
  have strongCode : lower.encode qStrong = ZFSet.pair (c.encode row)
      (assignmentCut levels alpha largerA) := SetMembers.raw_ofMem _ _
  intro sharedIdx hi rawU hu rawOldU hOldU rawW hw rawOldW hOldW newMember oldMember
  have newBound := newData _ newMember
  have oldBound := oldData _ oldMember
  obtain ⟨C, E, U, Rf, Rc, u, w, index, hu0, hw0, original, indexEq, termU, termW, edge⟩ :=
    M.semanticStructuralPrefix_assignmentImage_decode c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace member h A sharedIdx rawU rawW hi hu hw newMember
  subst sharedIdx rawU rawW
  let oldU : (M.nameDomain lower).names := ⟨⟨rawOldU, valid rawOldU hOldU⟩, M.transitive hT hOldU⟩
  let oldW : (M.nameDomain lower).names := ⟨⟨rawOldW, valid rawOldW hOldW⟩, M.transitive hT hOldW⟩
  obtain ⟨_sourceRow, _sourceA, _hSourceA, _sourceCondition, _sourceSubset,
      _k, _hk, _enumerations, _he, qOriginal, cut, _family, selected⟩ :=
    M.semanticStructuralPrefix_typed_assignment_certificates c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace member infinite choice prepared C E U Rf Rc index u.val w.val hu0 hw0 original
  obtain ⟨_, _, _, _, _, F0, B0, f0, e0, names0, _, _, _, _, _, _k0, _enum0, code0, _typed0⟩ := selected 0
  obtain ⟨_, _, _, _, _, F1, B1, f1, e1, names1, _, _, _, _, _, _k1, _enum1, code1, _typed1⟩ := selected 1
  have testFacts := M.semanticStructuralPrefix_aligned_cut_tests_at_larger_cut c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member r oldRow row A oldA largerA g h source oldSource
    belowOld oldBelowG belowH contains movedSubset oldSubset qOriginal qStrong cut strongCode
  have collisions := M.structuralAssignment_prepared_aligned_collision act lower t b d base directed alpha T T2
    system pairing unions powers separation collection hQ orderGround group nodes supports hAlpha hT meet descent
    small trace.1 exactStored I S mu positions tuples A (image (t.encode h) A) oldA liftedSupport
    g h D X V C E U Rf Rc u w oldU oldW index hu0 hw0 hOldU hOldW qOriginal qStrong
    testFacts.2.2.1 testFacts.2.2.2 relative overlap meetLeft meetRight meetGreatest
    ![F0, F1] ![B0, B1] ![f0, f1] ![e0, e1] ![names0, names1]
    original edge newBound oldBound contains testFacts.1 testFacts.2.1
    (Fin.cases code0 (Fin.cases code1 (fun j => Fin.elim0 j)))
  rw [strongCode] at collisions
  exact collisions

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

theorem solution.{u} : type_of% @OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefix_aligned_copy_crossCollisions_at_larger_cut_oai.{u} := @OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefix_aligned_copy_crossCollisions_at_larger_cut_oai.{u}
