-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralSuccessor_dense_visibleLift
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:39:55.847434+00:00
-- url     : https://prove2.me/submissions/4d3d23e5-c7b2-437e-89d9-fafd4ed6ba78

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
import Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_semanticStructuralSuccessor_insert_visibleLift

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
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall _root_.OAI.PartitionPilot.Forcing.Name.boundedNames_small _root_.OAI.PartitionPilot.Forcing.Name.unionIndices_small _root_.OAI.PartitionPilot.Forcing.PosetAction.mixIndices_small
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing



namespace SetFormula

open SetRealization
universe u
variable {P : Type u} [Preorder P] {s : Presentation P}

theorem forces_ex_iff (D : Name.NameDomain s) {n : Nat} (φ : SetFormula (n + 1))
    (env : Assignment D n) (p : P) :
    Forces D (ex φ) env p ↔ DenseBelow p {q | ∃ τ : D.names, Forces D φ (extend τ env) q} := by
  classical
  change (∀ q, q ≤ p → ¬ ∀ τ : D.names, ∀ r, r ≤ q → ¬ Forces D φ (extend τ env) r) ↔ _
  constructor
  · intro h q qp
    have witness := h q qp
    push Not at witness
    obtain ⟨τ, r, rq, hφ⟩ := witness
    exact ⟨r, rq, τ, hφ⟩
  · intro dense q qp allNeg
    obtain ⟨r, rq, τ, hφ⟩ := dense q qp
    exact allNeg τ r rq hφ

end SetFormula



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



namespace TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem ordinaryForces_congr_equalities (small : M.sets.Countable)
    (carrier : s.carrier ∈ M.sets) {n : Nat} (phi : SetFormula n)
    (env other : Assignment (M.nameDomain s) n) (p : P)
    (equal : ∀ j, Name.ForcesEq p (env j).val (other j).val) :
    Forces (M.nameDomain s) phi env p ↔ Forces (M.nameDomain s) phi other p := by
  have values (H : ConditionFilter P) (hp : H.mem p)
      (generic : H.GenericFor (formulaFamily (M.nameDomain s))) :
      evalAssignment {q | H.mem q} env = evalAssignment {q | H.mem q} other := by
    funext j
    exact Name.forcesEq_sound (M.nameDomain s) H
      (fun E hE dense => generic E (Or.inl hE) dense)
      (env j).val (env j).property (other j).val (other j).property p hp (equal j)
  rw [M.ordinaryForces_iff_all_generics s small carrier,
    M.ordinaryForces_iff_all_generics s small carrier]
  constructor
  · intro forced H hp generic
    rw [← values H hp generic]
    exact forced H hp generic
  · intro forced H hp generic
    rw [values H hp generic]
    exact forced H hp generic

theorem ordinaryForces_replace_first (small : M.sets.Countable)
    (carrier : s.carrier ∈ M.sets) {n : Nat} (phi : SetFormula (n + 1))
    (env : Assignment (M.nameDomain s) n) (sigma tau : (M.nameDomain s).names) (p : P)
    (equal : Name.ForcesEq p sigma.val tau.val) :
    Forces (M.nameDomain s) phi (extend sigma env) p ↔
      Forces (M.nameDomain s) phi (extend tau env) p :=
  M.ordinaryForces_congr_equalities s small carrier phi (extend sigma env) (extend tau env) p
    (Fin.cases equal (fun j => Name.forcesEq_refl (env j).val p))

end TransitiveGround



end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundAbsentLiftRangeCollisions
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
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)

theorem refinementVisibleLift_groundTerm_dense (small : M.sets.Countable)
    (U Rf Rc visibility target : (M.nameDomain s).names) (p : P) :
    let quotient : (M.nameDomain s).names := ⟨Name.refinementQuotient T valid U.val Rf.val,
      M.refinementQuotient_mem s pairing unions powers separation collection carrier order
        hT valid U.val Rf.val U.property Rf.property⟩
    let map := M.stageOneMapName s pairing unions powers separation collection carrier order
      hT valid U Rf Rc
    Forces (M.nameDomain s) refinementVisibleLiftFormula ![quotient, visibility, target, map] p →
    DenseBelow p {q | ∃ w : (M.nameDomain s).names, w.val.val ∈ T ∧
      Name.ForcesMem q w.val U.val ∧
      let fine := M.stageOneClassName s pairing unions powers separation collection carrier order
        hT valid Rf w
      Name.ForcesMem q fine.val visibility.val ∧
      Forces (M.nameDomain s) (BoundedFormula.pairMembershipFormula 0 1 2).toFormula
        ![fine, target, map] q} := by
  let quotient : (M.nameDomain s).names := ⟨Name.refinementQuotient T valid U.val Rf.val,
    M.refinementQuotient_mem s pairing unions powers separation collection carrier order
      hT valid U.val Rf.val U.property Rf.property⟩
  let map := M.stageOneMapName s pairing unions powers separation collection carrier order hT valid U Rf Rc
  let env : Assignment (M.nameDomain s) 4 := ![quotient, visibility, target, map]
  let phi : SetFormula 5 := .conj (.mem 0 2) (BoundedFormula.pairMembershipFormula 0 3 4).toFormula
  change Forces (M.nameDomain s) (ex (.conj (.mem 0 1) phi)) env p → _
  intro forced r rp
  obtain ⟨q, qr, rho, member, property⟩ :=
    (forces_ex_iff (M.nameDomain s) (.conj (.mem 0 1) phi) env p).1 forced r rp
  change Name.ForcesMem q rho.val quotient.val at member
  obtain ⟨v, vq, sigma, k, entry, vk, equal⟩ := member q le_rfl
  obtain ⟨w, hw, active, same⟩ :=
    (Name.entry_refinementQuotient T valid U.val Rf.val sigma k).1 entry
  let wName : (M.nameDomain s).names := ⟨w, M.transitive hT hw⟩
  let fine := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid Rf wName
  have sameFine : fine.val = sigma := same
  have equality : Name.ForcesEq v rho.val fine.val := sameFine.symm ▸ equal
  have propertyV : Forces (M.nameDomain s) phi (extend rho env) v :=
    forces_mono (M.nameDomain s) phi (extend rho env) property vq
  have selected : Forces (M.nameDomain s) phi (extend fine env) v :=
    (M.ordinaryForces_replace_first s small carrier phi env rho fine v equality).1 propertyV
  refine ⟨v, vq.trans qr, wName, hw, Name.forcesMem_mono active vk, ?_⟩
  exact selected

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





end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticRepresentedDomainLiftDecisions
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

theorem semanticStructuralSuccessor_dense_visibleLift_oai
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

    ∀ (C E : L) (U Rf Rc u : (M.nameDomain lower).names),
      let idx := refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
      idx ∈ M.niceRefinementIndices act lower b d alpha T T2 valid → u.val.val ∈ T →
      ∀ pCut r : SetMembers Q,
      lower.encode pCut = ZFSet.pair row (assignmentCut levels alpha A) → r ≤ pCut →
      Name.ForcesMem r u.val U.val →
      (∀ v z : (M.nameDomain lower).names, v.val.val ∈ T → z.val.val ∈ T →
        stageOneAssignment idx v.val.val z.val.val ∈ A →
        ∀ q, q ≤ r → ¬ Name.ForcesEq q (cls Rc u).val (cls Rc v).val) →
      let quotient : (M.nameDomain lower).names := ⟨Name.refinementQuotient T valid U.val Rf.val,
        M.refinementQuotient_mem lower pairing unions powers separation collection lowerGround lowerOrder
          hT valid U.val Rf.val U.property Rf.property⟩
      let map := M.stageOneMapName lower pairing unions powers separation collection
        lowerGround lowerOrder hT valid U Rf Rc
      Forces (M.nameDomain lower) refinementVisibleLiftFormula ![quotient, vis C, cls Rc u, map] r →
      DenseBelow r {q | ∃ w : (M.nameDomain lower).names, w.val.val ∈ T ∧
        Name.ForcesMem q u.val U.val ∧ Name.ForcesMem q w.val U.val ∧
        ∃ lowerRow lowerA : ZFSet.{u}, lower.encode q = ZFSet.pair lowerRow lowerA ∧
          let spliced := assignmentSplice levels alpha lowerA A
          let inserted := insert (stageOneAssignment idx u.val.val w.val.val) spliced
          ZFSet.pair lowerRow inserted ∈ upper ∧
          ZFSet.pair (ZFSet.pair lowerRow inserted) (ZFSet.pair row A) ∈
            M.refinementHistoryOrder c.carrier c.conditionOrder T (insert alpha alpha) next ∧
          A ⊆ inserted ∧ stageOneAssignment idx u.val.val w.val.val ∈ inserted ∧
          ZFSet.pair lowerRow (assignmentCut levels alpha inserted) = lower.encode q ∧
          Name.ForcesEq q (cls Rc u).val (cls Rc u).val} := by
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
  intro C E U Rf Rc u idx hu pCut r cutCode below active fresh existsLift k kr
  obtain ⟨q, qk, w, hw, activeW, visible, mapped⟩ :=
    M.refinementVisibleLift_groundTerm_dense lower pairing unions powers separation collection
      lowerGround lowerOrder hT valid small U Rf Rc (vis C) (cls Rc u) r existsLift k kr
  have qr := qk.trans kr
  have qp := qr.trans below
  have activeU := Name.forcesMem_mono active qr
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
  obtain ⟨insertCondition, insertCut, insertBelow⟩ :=
    M.semanticStructuralSuccessor_insert_visibleLift c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace member infinite small spliceCondition
      C E U Rf Rc u w idx hu hw q exactCut activeU activeW visible mapped
      (fun v z hv hz old j jq => fresh v z hv hz (oldOrigin v z hv hz old) j (jq.trans qr))
  have spliceOrder := (M.pair_mem_refinementHistoryOrder c.carrier c.conditionOrder T
    (insert alpha alpha) next _ _ _ _).1 spliceBelow
  have retained : A ⊆ insert (stageOneAssignment index u.val.val w.val.val) spliced :=
    fun _ ha => ZFSet.mem_insert_of_mem _ (spliceOrder.2.2.2 ha)
  refine ⟨q, qk, w, hw, activeU, activeW, lowerRow, lowerA, qCode,
    insertCondition, ?_, retained, ZFSet.mem_insert _ _, ?_, Name.forcesEq_refl _ _⟩
  · exact (M.pair_mem_refinementHistoryOrder c.carrier c.conditionOrder T
      (insert alpha alpha) next _ _ _ _).2
      ⟨insertCondition, condition, spliceOrder.2.2.1, retained⟩
  · rw [insertCut]
    exact exactCut.symm

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

theorem solution.{u} : type_of% @OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralSuccessor_dense_visibleLift_oai.{u} := @OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralSuccessor_dense_visibleLift_oai.{u}
