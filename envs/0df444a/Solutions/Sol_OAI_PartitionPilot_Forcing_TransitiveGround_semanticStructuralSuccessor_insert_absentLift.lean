-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralSuccessor_insert_absentLift
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:34:17.343193+00:00
-- url     : https://prove2.me/submissions/16bdc142-a00e-4028-a677-734b3918b9ee

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
universe u
variable {P : Type u} [Preorder P] {s : Presentation P}

theorem forcesEq_refl (σ : Name s) (p : P) : ForcesEq p σ σ := by
  induction σ using inductionOn generalizing p with
  | step σ ih =>
    rw [ForcesEq]
    constructor
    · intro ρ r hr q _ qr
      exact ⟨q, le_rfl, ρ, r, hr, qr, ih ρ r hr q⟩
    · intro ρ r hr q _ qr
      exact ⟨q, le_rfl, ρ, r, hr, qr, ih ρ r hr q⟩

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

namespace TransitiveGround

open SetRealization SetFormula Compression.RecursiveMaps
universe u v
variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P)

theorem codedFamily_countable (small : M.sets.Countable) : (M.codedFamily s).Countable :=
  small.image _

end TransitiveGround



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

variable (valid : ∀ z ∈ T, IsName s z)
variable (system : NiceNameSystem M a s b d base directed T valid)
variable (generic : H.GenericFor (formulaFamily (M.nameDomain s)))
variable (z : (M.nameDomain s).names)
variable (hs : HereditarilySymmetric a s (d.principalSupportFamily base directed) z.val)
variable (subset : Name.eval {p | H.mem p} z.val ⊆
  Name.eval {p | H.mem p} (Name.familySet ⊤ T valid))

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

include system generic subset descent in
theorem visibleSupportProfile_meet (v w : L)
    (left : b.encode v ∈ M.visibleSupportProfile a s b d T H (Name.eval {p | H.mem p} z.val))
    (right : b.encode w ∈ M.visibleSupportProfile a s b d T H (Name.eval {p | H.mem p} z.val)) :
    b.encode (meet v w) ∈ M.visibleSupportProfile a s b d T H (Name.eval {p | H.mem p} z.val) := by
  obtain ⟨x, hx, ex⟩ := (M.mem_eval_niceVisibilityName a s T (d.principalFix v) _ H.top_mem _).1
    ((M.encode_mem_visibleSupportProfile a s b d T H _ v).1 left)
  obtain ⟨y, hy, ey⟩ := (M.mem_eval_niceVisibilityName a s T (d.principalFix w) _ H.top_mem _).1
    ((M.encode_mem_visibleSupportProfile a s b d T H _ w).1 right)
  have dx := (M.name_mem_niceNameCandidates a s T (d.principalFix v) x).1 hx
  have dy := (M.name_mem_niceNameCandidates a s T (d.principalFix w) y).1 hy
  obtain ⟨τ, _, fixed, equal⟩ := descent v w ⟨x, dx.1⟩ ⟨y, dy.1⟩ dx.2.2 dy.2.2
    (system.candidate_hs v x hx) (system.candidate_hs w y hy) (ex.trans ey.symm)
  have target : Name.eval {p | H.mem p} τ.val = Name.eval {p | H.mem p} z.val := equal.trans ex
  have bounded : Name.eval {p | H.mem p} τ.val ⊆
      Name.eval {p | H.mem p} (Name.familySet ⊤ T valid) := target.symm ▸ subset
  apply (M.encode_mem_visibleSupportProfile a s b d T H _ (meet v w)).2
  exact target ▸ system.normalization_visible (meet v w) τ fixed H generic bounded

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

open SetRealization SetFormula
universe u

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

universe u

theorem mem_testedMeetFilter (F r e x : ZFSet.{u}) :
    x ∈ testedMeetFilter F r e ↔ x ∈ F ∧ ZFSet.pair e x ∈ r := by
  rw [testedMeetFilter, mem_relationImage]
  constructor
  · rintro ⟨hx, a, ha, edge⟩
    exact ⟨hx, (ZFSet.mem_singleton.1 ha) ▸ edge⟩
  · rintro ⟨hx, edge⟩
    exact ⟨hx, e, ZFSet.mem_singleton.2 rfl, edge⟩

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
variable (s : Presentation P) (carrier : s.carrier ∈ M.sets)
variable (a : PosetAction G P) (b : Presentation L) (d : PosetAction G L)
variable {T : ZFSet.{u}} (valid : ∀ z ∈ T, IsName s z)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)

include carrier in
theorem absentLift_profile_inequalities (small : M.sets.Countable)
    (C K : L) (moved old : (M.nameDomain s).names) (profile : ZFSet.{u})
    (r q : P) (below : q ≤ r)
    (decisions : M.DecidesVisibilityProfile a s b d.principalFix T profile old.val r)
    (survivor : b.encode C ∉ profile → b.encode K ∉ profile) :
    let vis := M.stageOneVisibilityName s valid a b d base directed system
    Name.ForcesMem q moved.val (vis K).val →
    (∀ p, p ≤ q → ¬ Name.ForcesMem p moved.val (vis C).val) →
    (∀ p, p ≤ q → ¬ Name.ForcesEq p moved.val old.val) ∧
    (∀ p, p ≤ q → ¬ Name.ForcesEq p old.val moved.val) := by
  dsimp only
  let vis := M.stageOneVisibilityName s valid a b d base directed system
  intro visible absent
  have negative : Forces (M.nameDomain s) (.neg (.equal 0 1)) ![moved, old] q := by
    apply (M.ordinaryForces_iff_all_generics s small carrier _ _ q).2
    intro H hq generic same
    change Name.eval {p | H.mem p} moved.val = Name.eval {p | H.mem p} old.val at same
    classical
    by_cases atC : b.encode C ∈ profile
    · have oldVisible := Name.forcesMem_mono ((decisions C).1 atC) below
      have seen := Name.forcesMem_sound (M.nameDomain s) H
        (fun D hD dense => generic D (Or.inl hD) dense)
        old.property (vis C).property hq oldVisible
      have movedNegative : Forces (M.nameDomain s) (.neg (.mem 0 1)) ![moved, vis C] q := absent
      have unseen : Name.eval {p | H.mem p} moved.val ∉ Name.eval {p | H.mem p} (vis C).val :=
        forces_sound (M.nameDomain s) H generic (.neg (.mem 0 1)) ![moved, vis C] hq movedNegative
      exact unseen (same.symm ▸ seen)
    · have oldNegative : Forces (M.nameDomain s) (.neg (.mem 0 1)) ![old, vis K] q :=
        fun p pq => (decisions K).2 (survivor atC) p (pq.trans below)
      have unseen : Name.eval {p | H.mem p} old.val ∉ Name.eval {p | H.mem p} (vis K).val :=
        forces_sound (M.nameDomain s) H generic (.neg (.mem 0 1)) ![old, vis K] hq oldNegative
      have seen := Name.forcesMem_sound (M.nameDomain s) H
        (fun D hD dense => generic D (Or.inl hD) dense)
        moved.property (vis K).property hq visible
      exact unseen (same ▸ seen)
  exact ⟨negative, fun p pq equal => negative p pq (Name.forcesEq_symm equal)⟩

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (order : s.conditionOrder ∈ M.sets) (hT : T ∈ M.sets)

theorem refinementAbsentLift_profile_collisions (small : M.sets.Countable)
    (C K : L) (Rf Rc u oldU w oldW : (M.nameDomain s).names)
    (profile : ZFSet.{u}) (r q : P) (below : q ≤ r) :
    let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
    let vis := M.stageOneVisibilityName s valid a b d base directed system
    M.DecidesVisibilityProfile a s b d.principalFix T profile (cls Rf oldW).val r →
    (b.encode C ∉ profile → b.encode K ∉ profile) →
    Name.ForcesMem q (cls Rf w).val (vis K).val →
    (∀ p, p ≤ q → ¬ Name.ForcesMem p (cls Rf w).val (vis C).val) →
    (∀ p, p ≤ q → ¬ Name.ForcesEq p (cls Rc u).val (cls Rc oldU).val) →
    (∀ p, p ≤ q → ¬ Name.ForcesEq p (cls Rf w).val (cls Rf oldW).val) ∧
    (∀ p, p ≤ q → ¬ Name.ForcesEq p (cls Rf oldW).val (cls Rf w).val) ∧
    M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid
      Rf Rc u oldU w oldW q ∧
    M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid
      Rf Rc oldU u oldW w q ∧
    M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid
      Rf Rc u u w w q := by
  dsimp only
  let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
  intro decisions survivor visible absent coarseDifferent
  obtain ⟨fineDifferent, fineDifferent'⟩ := M.absentLift_profile_inequalities s carrier a b d valid
    base directed system small C K (cls Rf w) (cls Rf oldW) profile r q below
    decisions survivor visible absent
  have collision : M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid
      Rf Rc u oldU w oldW q := by
    constructor
    · intro p pq facts
      exact coarseDifferent p pq facts.1
    · intro p pq facts
      exact fineDifferent p pq facts.1
  exact ⟨fineDifferent, fineDifferent', collision,
    M.stageOneCollisionTest_symm s pairing unions powers separation collection carrier order hT valid
      Rf Rc u oldU w oldW q collision,
    M.stageOneCollisionTest_self s pairing unions powers separation collection carrier order hT valid
      small Rf Rc u w q⟩

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

namespace RecursiveRefinementOrderHistory
variable {M : TransitiveGround.{u}} {rows rowOrder T stages history : ZFSet.{u}}
variable (run : RecursiveRefinementOrderHistory M rows rowOrder T stages history)
include run

theorem restrict {earlier : ZFSet.{u}} (ordinal : ordinalSetProperty earlier)
    (subset : earlier ⊆ stages) :
    RecursiveRefinementOrderHistory M rows rowOrder T earlier (graphRestriction earlier history) := by
  refine ⟨run.carriers.restrict ordinal subset, ?_⟩
  intro beta d entry
  have packed := (pair_mem_graphRestriction.1 entry).1
  have hbeta := (pair_mem_graphRestriction.1 entry).2
  rw [graphRestriction_restrict (ordinal.1 beta hbeta)]
  exact run.order beta d packed

end RecursiveRefinementOrderHistory





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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundRefinementAbsentLiftInsertions
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
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
variable (a : PosetAction G P) (b : Presentation L) (d : PosetAction G L)
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

include descent in
theorem stageOneSingleTests_absentLift_caps (small : M.sets.Countable)
    (C E K : L) (U Rf Rc u w : (M.nameDomain s).names) (F : ZFSet.{u})
    (p : P) (activeU : Name.ForcesMem p u.val U.val)
    (activeW : Name.ForcesMem p w.val U.val)
    (capPositive : ∀ v : L, b.encode v ∈ testedMeetFilter F b.conditionOrder (b.encode E) → K ≤ v)
    (capNegative : ∀ v : L, E ≤ v →
      b.encode v ∉ testedMeetFilter F b.conditionOrder (b.encode E) → meet K v = C) :
    let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
    let vis := M.stageOneVisibilityName s valid a b d base directed system
    M.DecidesVisibilityProfile a s b d.principalFix T F (cls Rc u).val p →
    Name.ForcesMem p (cls Rf w).val (vis K).val →
    (∀ q, q ≤ p → ¬ Name.ForcesMem q (cls Rf w).val (vis C).val) →
    M.stageOneSingleTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system C E U Rf Rc u w p := by
  dsimp only
  let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
  let vis := M.stageOneVisibilityName s valid a b d base directed system
  intro decisions capVisible nonvisible
  have negativeC : Forces (M.nameDomain s) (.neg (.mem 0 1)) ![cls Rf w, vis C] p := nonvisible
  refine ⟨⟨activeU, activeW⟩, ?_, ?_⟩
  · intro v above
    apply (M.ordinaryForces_iff_all_joint_generics s small carrier _ _ p).2
    intro H hp coded generic
    let evaluated : TransitiveGround.{u} :=
      ⟨(M.nameDomain s).values {q | H.mem q}, (M.nameDomain s).values_transitive _⟩
    apply (evaluated.realize_refinementProfileFormula _ (fun j => ⟨_, rfl⟩)).2
    have capSeen := Name.forcesMem_sound (M.nameDomain s) H
      (fun D hD dense => generic D (Or.inl hD) dense)
      (cls Rf w).property (vis K).property hp capVisible
    have notSeen : Name.eval {q | H.mem q} (cls Rf w).val ∉
        Name.eval {q | H.mem q} (vis C).val :=
      forces_sound (M.nameDomain s) H generic (.neg (.mem 0 1)) ![cls Rf w, vis C] hp negativeC
    by_cases member : b.encode v ∈ F
    · have tested := (mem_testedMeetFilter F b.conditionOrder (b.encode E) (b.encode v)).2
        ⟨member, (b.pair_mem_conditionOrder E v).2 above⟩
      have fineSeen := (M.encode_mem_visibleSupportProfile a s b d T H _ v).1
        (M.visibleSupportProfile_upward a s b d T H _ (capPositive v tested)
          ((M.encode_mem_visibleSupportProfile a s b d T H _ K).2 capSeen))
      have coarsePositive : Forces (M.nameDomain s) (.mem 0 1) ![cls Rc u, vis v] p :=
        (decisions v).1 member
      have coarseSeen := forces_sound (M.nameDomain s) H generic (.mem 0 1)
        ![cls Rc u, vis v] hp coarsePositive
      exact ⟨fun _ => fineSeen, fun _ => coarseSeen⟩
    · have notTested : b.encode v ∉ testedMeetFilter F b.conditionOrder (b.encode E) :=
        fun yes => member ((mem_testedMeetFilter F b.conditionOrder (b.encode E) (b.encode v)).1 yes).1
      have coarseNegative : Forces (M.nameDomain s) (.neg (.mem 0 1)) ![cls Rc u, vis v] p :=
        (decisions v).2 member
      have coarseNotSeen := forces_sound (M.nameDomain s) H generic (.neg (.mem 0 1))
        ![cls Rc u, vis v] hp coarseNegative
      have fineNotSeen : Name.eval {q | H.mem q} (cls Rf w).val ∉
          Name.eval {q | H.mem q} (vis v).val := by
        intro fineSeen
        have bounded := Name.eval_subset_familySet_of_code_subset H T valid (cls Rf w).val
          (Name.refinementClass_subset T valid Rf.val w.val)
        have overlap := M.visibleSupportProfile_meet a s b d base directed T H valid system generic
          (cls Rf w) bounded meet (descent H coded generic) K v
          ((M.encode_mem_visibleSupportProfile a s b d T H _ K).2 capSeen)
          ((M.encode_mem_visibleSupportProfile a s b d T H _ v).2 fineSeen)
        rw [capNegative v above notTested] at overlap
        exact notSeen ((M.encode_mem_visibleSupportProfile a s b d T H _ C).1 overlap)
      exact ⟨fun yes => False.elim (coarseNotSeen yes), fun yes => False.elim (fineNotSeen yes)⟩
  · apply (M.ordinaryForces_iff_all_generics s small carrier _ _ p).2
    intro H hp generic
    let evaluated : TransitiveGround.{u} :=
      ⟨(M.nameDomain s).values {q | H.mem q}, (M.nameDomain s).values_transitive _⟩
    apply (evaluated.realize_refinementCompatibilityFormula _ (fun j => ⟨_, rfl⟩)).2
    intro seen
    exact False.elim ((forces_sound (M.nameDomain s) H generic (.neg (.mem 0 1))
      ![cls Rf w, vis C] hp negativeC) seen)

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P)
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

variable (small : M.sets.Countable)
include indices nodes small descent

theorem refinementLevelRawTests_insert_absentLift
    (C E K : L) (U Rf Rc u w : (M.nameDomain s).names) (F : ZFSet.{u})
    (member : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d level T T2 valid)
    {A : ZFSet.{u}} (p : P)
    (tests : stageOneRawTests M (M.refinementLevelFormulaData a s b d level T T2 valid) A (s.encode p))
    (activeU : Name.ForcesMem p u.val U.val) (activeW : Name.ForcesMem p w.val U.val)
    (capPositive : ∀ v : L, b.encode v ∈ testedMeetFilter F b.conditionOrder (b.encode E) → K ≤ v)
    (capNegative : ∀ v : L, E ≤ v →
      b.encode v ∉ testedMeetFilter F b.conditionOrder (b.encode E) → meet K v = C) :
    let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
    let vis := M.stageOneVisibilityName s valid a b d base directed system
    M.DecidesVisibilityProfile a s b d.principalFix T F (cls Rc u).val p →
    Name.ForcesMem p (cls Rf w).val (vis K).val →
    (∀ q, q ≤ p → ¬ Name.ForcesMem q (cls Rf w).val (vis C).val) →
    (∀ (v z : (M.nameDomain s).names), v.val.val ∈ T → z.val.val ∈ T →
      stageOneAssignment (refinementIndexCode level (b.encode C) (b.encode E)
        U.val.val Rf.val.val Rc.val.val) v.val.val z.val.val ∈ A →
      (∀ q, q ≤ p → ¬ Name.ForcesEq q (cls Rc u).val (cls Rc v).val) ∧
      ∃ profile, M.DecidesVisibilityProfile a s b d.principalFix T profile (cls Rf z).val p ∧
        (b.encode C ∉ profile → b.encode K ∉ profile)) →
    stageOneRawTests M (M.refinementLevelFormulaData a s b d level T T2 valid)
      (insert (stageOneAssignment (refinementIndexCode level (b.encode C) (b.encode E)
        U.val.val Rf.val.val Rc.val.val) u.val.val w.val.val) A) (s.encode p) := by
  dsimp only
  let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
  let vis := M.stageOneVisibilityName s valid a b d base directed system
  intro decisions capVisible nonvisible oldProfiles
  have single := M.refinementLevelRawSingle_iff a s b d level pairing unions powers separation collection
    carrier order nodes hT valid indices base directed system
  have collision := M.refinementLevelRawCollision_iff a s b d level pairing unions powers separation collection
    carrier order hT valid indices
  have mixed (v z : (M.nameDomain s).names) (hv : v.val.val ∈ T) (hz : z.val.val ∈ T)
      (old : stageOneAssignment (refinementIndexCode level (b.encode C) (b.encode E)
        U.val.val Rf.val.val Rc.val.val) v.val.val z.val.val ∈ A) :
      M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid
        Rf Rc u v w z p ∧
      M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid
        Rf Rc v u z w p := by
    obtain ⟨different, profile, profileDecisions, survivor⟩ := oldProfiles v z hv hz old
    have facts := M.refinementAbsentLift_profile_collisions s carrier a b d valid base directed system
      pairing unions powers separation collection order hT small C K Rf Rc u v w z profile p p le_rfl
      profileDecisions survivor capVisible nonvisible different
    exact ⟨facts.2.2.1, facts.2.2.2.1⟩
  apply stageOneRawTests_insert M (M.refinementLevelFormulaData a s b d level T T2 valid) tests
  · exact (single C E U Rf Rc u w member p).2
      (M.stageOneSingleTests_absentLift_caps s pairing unions powers separation collection carrier order hT valid
        a b d base directed system meet descent small C E K U Rf Rc u w F p
        activeU activeW capPositive capNegative decisions capVisible nonvisible)
  · intro v hv z hz old
    let vn : (M.nameDomain s).names := ⟨⟨v, valid v hv⟩, M.transitive hT hv⟩
    let zn : (M.nameDomain s).names := ⟨⟨z, valid z hz⟩, M.transitive hT hz⟩
    exact (collision C E U Rf Rc vn u zn w member p).2 (mixed vn zn hv hz old).2
  · intro v hv z hz old
    let vn : (M.nameDomain s).names := ⟨⟨v, valid v hv⟩, M.transitive hT hv⟩
    let zn : (M.nameDomain s).names := ⟨⟨z, valid z hz⟩, M.transitive hT hz⟩
    exact (collision C E U Rf Rc u vn w zn member p).2 (mixed vn zn hv hz old).1
  · exact (collision C E U Rf Rc u u w w member p).2
      (M.stageOneCollisionTest_self s pairing unions powers separation collection carrier order hT valid
        small Rf Rc u w p)

end PartitionPilot.Forcing.TransitiveGround

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

theorem semanticStructuralSuccessor_insert_absentLift_oai
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0) (small : M.sets.Countable)
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

    ∀ (meet : L → L → L),
      (∀ (H : ConditionFilter (SetMembers Q)), H.GenericFor (M.codedFamily lower) →
        H.GenericFor (formulaFamily (M.nameDomain lower)) →
        ∀ (v z : L) (x y : (M.nameDomain lower).names),
          d.principalFix v ≤ (act).stabilizer lower x.val →
          d.principalFix z ≤ (act).stabilizer lower y.val →
          HereditarilySymmetric act lower (d.principalSupportFamily base directed) x.val →
          HereditarilySymmetric act lower (d.principalSupportFamily base directed) y.val →
          Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
          ∃ tau : (M.nameDomain lower).names,
            HereditarilySymmetric act lower (d.principalSupportFamily base directed) tau.val ∧
            d.principalFix (meet v z) ≤ (act).stabilizer lower tau.val ∧
            Name.eval {p | H.mem p} tau.val = Name.eval {p | H.mem p} x.val) →
    ∀ (C E K : L) (U Rf Rc u w : (M.nameDomain lower).names) (F : ZFSet.{u}),
      let idx := refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
      idx ∈ M.niceRefinementIndices act lower b d alpha T T2 valid →
      u.val.val ∈ T → w.val.val ∈ T →
      ∀ pCut q : SetMembers Q,
      lower.encode pCut = ZFSet.pair row (assignmentCut levels alpha A) → q ≤ pCut →
      Name.ForcesMem q u.val U.val → Name.ForcesMem q w.val U.val →
      (∀ v : L, b.encode v ∈ testedMeetFilter F b.conditionOrder (b.encode E) → K ≤ v) →
      (∀ v : L, E ≤ v → b.encode v ∉ testedMeetFilter F b.conditionOrder (b.encode E) → meet K v = C) →
      M.DecidesVisibilityProfile act lower b d.principalFix T F (cls Rc u).val q →
      Name.ForcesMem q (cls Rf w).val (vis K).val →
      (∀ p, p ≤ q → ¬ Name.ForcesMem p (cls Rf w).val (vis C).val) →
      (∀ v z : (M.nameDomain lower).names, v.val.val ∈ T → z.val.val ∈ T →
        stageOneAssignment idx v.val.val z.val.val ∈ A →
        (∀ p, p ≤ q → ¬ Name.ForcesEq p (cls Rc u).val (cls Rc v).val) ∧
        ∃ profile, M.DecidesVisibilityProfile act lower b d.principalFix T profile (cls Rf z).val q ∧
          (b.encode C ∉ profile → b.encode K ∉ profile)) →
      ∃ lowerRow lowerA : ZFSet.{u}, lower.encode q = ZFSet.pair lowerRow lowerA ∧
        let spliced := assignmentSplice levels alpha lowerA A
        let inserted := insert (stageOneAssignment idx u.val.val w.val.val) spliced
        ZFSet.pair lowerRow inserted ∈ upper ∧
        ZFSet.pair (ZFSet.pair lowerRow inserted) (ZFSet.pair row A) ∈
          M.refinementHistoryOrder c.carrier c.conditionOrder T (insert alpha alpha) next ∧
        A ⊆ inserted ∧ stageOneAssignment idx u.val.val w.val.val ∈ inserted ∧
        ZFSet.pair lowerRow (assignmentCut levels alpha inserted) = lower.encode q ∧
        Name.ForcesEq q (cls Rc u).val (cls Rc u).val := by
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
  let cls := M.stageOneClassName lower pairing unions powers separation collection lowerGround lowerOrder hT valid
  let vis := M.stageOneVisibilityName lower valid act b d base directed system.first
  dsimp only
  intro meet descent C E K U Rf Rc u w F idx hu hw pCut q cutCode qp
    activeU activeW capPositive capNegative decisions capVisible nonvisible oldProfiles
  obtain ⟨lowerRow, _, lowerA, _, qCode⟩ := ZFSet.mem_prod.1
    (M.refinementHistoryForcing_shape c.carrier T alpha lowerPacked (SetMembers.raw_mem q))
  change lower.encode q = ZFSet.pair lowerRow lowerA at qCode
  have alphaNext : alpha ⊆ insert alpha alpha := fun _ h => ZFSet.mem_insert_of_mem _ h
  have nextSubset : insert alpha alpha ⊆ stages := by
    intro x hx
    exact (ZFSet.mem_insert_iff.1 hx).elim (fun e => e ▸ member) (fun h => subset x h)
  have nextOrdinal := ordinalSetProperty_succ cutOrdinal
  let nextRun := (run).restrict nextOrdinal nextSubset
  have nextGround : insert alpha alpha ∈ M.sets := M.insert_mem pairing unions hAlpha hAlpha
  have packedNextGround : next ∈ M.sets := M.graphRestriction_mem unions separation nextGround packedGround
  have witnesses := M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace
  have mono := M.structuralHistory_rawTests_mono t b d base directed T T2 stages history
    pairing unions powers separation collection group nodes supports hh hT witnesses
  have lowerBelow : ZFSet.pair (ZFSet.pair lowerRow lowerA)
      (ZFSet.pair row (assignmentCut levels alpha A)) ∈
      M.refinementHistoryOrder c.carrier c.conditionOrder T alpha (graphRestriction alpha next) := by
    rw [graphRestriction_restrict alphaNext]
    change ZFSet.pair (lower.encode q) (lower.encode pCut) ∈ _ at qp
    rwa [qCode, cutCode] at qp
  obtain ⟨spliceCondition, spliceBelow, spliceCut⟩ := nextRun.splice_lifting
    pairing unions powers separation infinite choice nextGround packedNextGround hT hAlpha
    nextOrdinal cutOrdinal alphaNext
    (fun beta fields entry => mono beta fields (pair_mem_graphRestriction.1 entry).1)
    condition lowerBelow
  let spliced := assignmentSplice levels alpha lowerA A
  have exactCut : lower.encode q = ZFSet.pair lowerRow (assignmentCut levels alpha spliced) := by
    rw [spliceCut]
    exact qCode
  have stored := M.semanticStructuralPrefix_refinementData_entry c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  have storedNext := pair_mem_graphRestriction.2 ⟨stored, ZFSet.mem_insert alpha alpha⟩
  let fields := M.refinementLevelFormulaData act lower b d alpha T T2 valid
  let index := refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
  have indexMem : index ∈ fields 0 := idx
  have oldOrigin (v z : (M.nameDomain lower).names) (hv : v.val.val ∈ T) (hz : z.val.val ∈ T)
      (old : stageOneAssignment index v.val.val z.val.val ∈ spliced) :
      stageOneAssignment index v.val.val z.val.val ∈ A := by
    rcases (mem_assignmentSplice levels alpha lowerA A _).1 old with low | high
    · obtain ⟨_, xi, hxi, edge⟩ := low
      have same := (nextRun.carriers.data.assignment_level_iff storedNext index indexMem
        v.val.val hv z.val.val hz xi).1 edge
      exact False.elim (ZFSet.mem_irrefl alpha (same ▸ hxi))
    · exact high.1
  have same := (run).carriers.stored_successor_eq ordinal member fields stored
  have old := (M.pair_mem_stageTwoConditions c.carrier
    (refinementDataHistoryIndices (insert alpha alpha) next) levels alpha fields lowerRow spliced).1
      (same ▸ spliceCondition)
  have oldTests : stageOneRawTests M fields spliced (lower.encode q) := by
    rw [exactCut]
    exact old.2.2.2.2.2
  have allTests := M.refinementLevelRawTests_insert_absentLift act lower b d alpha
    pairing unions powers separation collection lowerGround lowerOrder nodes hT valid system.indices
    base directed system.first meet descent small C E K U Rf Rc u w F idx q oldTests
    activeU activeW capPositive capNegative decisions capVisible nonvisible
    (fun v z hv hz old => oldProfiles v z hv hz (oldOrigin v z hv hz old))
  have inserted : stageOneAssignment index u.val.val w.val.val ∈
      insert (stageOneAssignment index u.val.val w.val.val) spliced := ZFSet.mem_insert _ _
  rw [exactCut] at allTests
  obtain ⟨insertCondition, insertCut, _⟩ :=
    (run).carriers.stored_successor_insert_extension pairing unions powers separation infinite
      ordinal member fields stored system.indices.index_ground hT c.conditionOrder c.conditionOrder_code
      indexMem hu hw spliceCondition (allTests.1 index indexMem _ hu _ hw inserted)
      (fun v hv z hz old => allTests.2 index indexMem v hv _ hu z hz _ hw
        (ZFSet.mem_insert_of_mem _ old) inserted)
      (fun v hv z hz old => allTests.2 index indexMem _ hu v hv _ hw z hz
        inserted (ZFSet.mem_insert_of_mem _ old))
      (allTests.2 index indexMem _ hu _ hu _ hw _ hw inserted inserted)
  have spliceOrder := (M.pair_mem_refinementHistoryOrder c.carrier c.conditionOrder T
    (insert alpha alpha) next _ _ _ _).1 spliceBelow
  have retained : A ⊆ insert (stageOneAssignment index u.val.val w.val.val) spliced :=
    fun _ ha => ZFSet.mem_insert_of_mem _ (spliceOrder.2.2.2 ha)
  refine ⟨lowerRow, lowerA, qCode, insertCondition, ?_, retained, inserted, ?_, Name.forcesEq_refl _ _⟩
  · exact (M.pair_mem_refinementHistoryOrder c.carrier c.conditionOrder T
      (insert alpha alpha) next _ _ _ _).2
      ⟨insertCondition, condition, spliceOrder.2.2.1, retained⟩
  · rw [insertCut]
    exact exactCut.symm

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

theorem solution.{u} : type_of% @OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralSuccessor_insert_absentLift_oai.{u} := @OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralSuccessor_insert_absentLift_oai.{u}
