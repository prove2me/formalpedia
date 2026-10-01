-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.proposition_2_3
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T17:32:06.131483+00:00
-- url     : https://prove2.me/submissions/26c0e221-9ff2-4723-b766-782c86b0a8f2

import Definitions.Def_LocalConjugacy_Groups
import Definitions.Def_LocalConjugacy_Cohomology
import Definitions.Def_LocalConjugacy_Examples
import Definitions.Def_LocalConjugacy_Proof_Definitions
import Definitions.Def_LocalConjugacy_Proof_Bridges
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_Heisenberg
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_HeisenbergStructure
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_HeisenbergSupersolvable
import Definitions.Def_LocalConjugacy_Proof_ConcreteGroups
import Definitions.Def_LocalConjugacy_Targets
import Definitions.Def_LocalConjugacy_Proof_Compactness
import Definitions.Def_LocalConjugacy_Proof_ProfiniteSylow
import Definitions.Def_LocalConjugacy_Proof_StructuralImages
import Definitions.Def_LocalConjugacy_Proof_FiniteAbelianCohomology
import Definitions.Def_LocalConjugacy_Proof_AbelianComplement
import Definitions.Def_LocalConjugacy_Proof_QuotientReduction
import Definitions.Def_LocalConjugacy_Proof_Cohomology
import Definitions.Def_LocalConjugacy_Proof_InvariantRestriction
import Definitions.Def_LocalConjugacy_Proof_CocycleActions
import Definitions.Def_LocalConjugacy_Proof_CoprimeCohomology
import Definitions.Def_LocalConjugacy_Proof_CocycleDescent
import Definitions.Def_LocalConjugacy_Proof_CocycleZorn
import Definitions.Def_LocalConjugacy_Proof_CocycleProducts
import Definitions.Def_LocalConjugacy_Proof_FiniteCoefficientSubgroup
import Definitions.Def_LocalConjugacy_Proof_CocycleInvarianceSubgroup
import Definitions.Def_LocalConjugacy_Proof_CocycleInjectivity
import Definitions.Def_LocalConjugacy_Proof_CocycleRebase
import Definitions.Def_LocalConjugacy_Proof_FiniteHall
import Definitions.Def_LocalConjugacy_Proof_SupersolvableStructure
import Definitions.Def_LocalConjugacy_Proof_ProfiniteHall
import Definitions.Def_LocalConjugacy_Proof_ActionProductTopology
import Definitions.Def_LocalConjugacy_Proof_HallCohomology
import Definitions.Def_LocalConjugacy_Proof_SupersolvableRestriction
import Definitions.Def_LocalConjugacy_Proof_NilpotentCoefficients
import Definitions.Def_LocalConjugacy_Proof_NonabelianComplement
import Definitions.Def_LocalConjugacy_Proof_ComplementSupersolvable
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_Quaternion
import Definitions.Def_LocalConjugacy_Proof_QuaternionCohomology
import Definitions.Def_LocalConjugacy_Proof_QuaternionMatrices
import Definitions.Def_LocalConjugacy_Proof_QuaternionAction
import Definitions.Def_LocalConjugacy_Proof_QuaternionComplements
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_FiniteSubgroupSystem_map_subgroup
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_cutoff_hall_isComplement
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_extend_cocycle_across_trivial_factor
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_hall_complement_restriction
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_prosupersolvable_action_trivial_on_high_primes
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_subgroup_quotient_factors

/-! Kernel-checked proof and its local helpers, retaining their original scopes. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

section Algebra
variable {G F : Type*} [Group G] [Group F]





end Algebra

section Topology
variable {G F : Type*} [Group G] [Group F]
  [TopologicalSpace G] [TopologicalSpace F] [DiscreteTopology F]



/-- A continuous discrete quotient of a prosupersolvable group is
supersolvable, with the actual normal cyclic series transported. -/
private theorem supersolvable_of_prosupersolvable_surjective (hG : Prosupersolvable G)
    (f : G →* F) (hf : Continuous f) (hs : Function.Surjective f) : Supersolvable F := by
  let U : OpenNormalSubgroup G :=
    { toSubgroup := f.ker
      isOpen' := hf.isOpen_preimage _ (isOpen_discrete {1}) }
  exact supersolvable_of_surjective (hG U) (QuotientGroup.kerLift f)
    (QuotientGroup.lift_surjective_of_surjective _ f hs le_rfl)



end Topology

section Discrete
variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]





end Discrete
end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

namespace FiniteSubgroupSystem
open FiniteSylowSystem
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]
variable (S : (U : OpenNormalSubgroup G) → Subgroup (G ⧸ U.toSubgroup))
variable (hS : ∀ (U V : OpenNormalSubgroup G) (h : U ≤ V),
  (S U).map (transition h) = S V)





private theorem subgroup_closed : IsClosed (subgroup S : Set G) := by
  rw [show (subgroup S : Set G) = ⋂ U : OpenNormalSubgroup G,
    (QuotientGroup.mk' U.toSubgroup) ⁻¹' (S U).carrier by
      ext x
      simp only [Set.mem_iInter, Set.mem_preimage]
      exact mem_subgroup S x]
  apply isClosed_iInter
  intro U
  have hc : IsClosed (S U).carrier := isClosed_discrete _
  exact hc.preimage (continuous_quotient_mk' : Continuous (QuotientGroup.mk' U.toSubgroup))

include hS








end FiniteSubgroupSystem

section ProfiniteHall
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]
open FiniteSylowSystem
open scoped Pointwise



















private theorem upperHall_isHallPro (hG : Prosupersolvable G) (n : ℕ) :
    IsHallPro {p | n < p} (upperHall hG n) := by
  refine ⟨FiniteSubgroupSystem.subgroup_closed _, fun U => ?_⟩
  change IsHall _ ((FiniteSubgroupSystem.subgroup _).map _)
  rw [FiniteSubgroupSystem.map_subgroup _ (finiteUpperHall_transition hG n)]
  exact finiteUpperHall_hall hG n U

namespace HallComplementSystem
open CategoryTheory
variable (hG : Prosupersolvable G) (n : ℕ) (P : Subgroup G)









end HallComplementSystem



end ProfiniteHall
end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy



private theorem HasPrimes.of_surjective {G F : Type*} [Group G] [Group F] {π : Set ℕ}
    (hG : HasPrimes π G) (f : G →* F) (hf : Function.Surjective f) : HasPrimes π F :=
  fun p hp hd => hG p hp (hd.trans (Subgroup.card_dvd_of_surjective f hf))

private theorem HasProPrimes.of_ambient_images {G : Type*} [Group G] [TopologicalSpace G]
    [Profinite G] {π : Set ℕ} (H : Subgroup G)
    (hH : ∀ U : OpenNormalSubgroup G, HasPrimes π (H.map (QuotientGroup.mk' U.toSubgroup))) :
    HasProPrimes π H := by
  intro V
  obtain ⟨U, f, hf⟩ := subgroup_quotient_factors H V
  exact (hH U).of_surjective f hf

private theorem IsHallPro.hasProPrimes {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]
    {π : Set ℕ} {H : Subgroup G} (hH : IsHallPro π H) : HasProPrimes π H :=
  HasProPrimes.of_ambient_images H (fun U => (hH.2 U).1)











section Cocycles
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [IsTopologicalGroup N]
  [MulDistribMulAction J N] [ContinuousSMul J N]





end Cocycles
end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy



section Action
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [DiscreteTopology N] [Finite N]
  [MulDistribMulAction J N] [ContinuousSMul J N]

private theorem prosupersolvable_acting_group (hG : Prosupersolvable (ActionProduct J N)) :
    Prosupersolvable J := by
  intro U
  exact supersolvable_of_prosupersolvable_surjective hG
    ((QuotientGroup.mk' U.toSubgroup).comp SemidirectProduct.rightHom)
    (continuous_quotient_mk'.comp actionProduct_continuous_right)
    ((QuotientGroup.mk'_surjective U.toSubgroup).comp SemidirectProduct.rightHom_surjective)





end Action
end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

/-!
Proposition 2.3 (`prop:res_pi`) of the current manuscript. The Hall subgroup
`Q` is arbitrary, not just the complement chosen in a structural existence
theorem. The proof follows the paper: construct the normal high-prime factor
`M`, show that it centralizes `N`, and extend by `φ(mq) = φ(q)`.
-/

namespace LocalConjugacy



section Numbered
variable {J N : Type*} [Group J] [Group N] [TopologicalSpace J]
  [TopologicalSpace N] [MulDistribMulAction J N]

/-- Proposition 2.3: restriction is bijective onto all of `H¹(Q,N)`.
The `N_p` in the printed statement is interpreted as `N`, which is a p-group. -/
private theorem proposition_2_3_preparedProof [Profinite J] [DiscreteTopology N] [Finite N]
    [ContinuousSMul J N]
    (p : ℕ) (hp : p.Prime) (hN : IsPGroup p N)
    (hG : Prosupersolvable (ActionProduct J N))
    (Q : Subgroup J) (hQ : IsHallPro {r | r ≤ p} Q) :
    Function.Bijective (restrictH1 (N := N) (show Q ≤ ⊤ from le_top)) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hJs := prosupersolvable_acting_group hG
  let M := upperHall hJs p
  have hM := upperHall_isHallPro hJs p
  have hMQ := cutoff_hall_isComplement M Q hM hQ
  have hact := prosupersolvable_action_trivial_on_high_primes hG hN M hM.hasProPrimes
  have hres := hall_complement_restriction hN M Q hM.1 hQ.1 hMQ hM.hasProPrimes hact
  constructor
  · intro a b hab
    induction a using Quotient.inductionOn with
    | h f =>
      induction b using Quotient.inductionOn with
      | h g =>
        exact Quotient.sound (hres.1 f g (Quotient.exact hab))
  · intro b
    induction b using Quotient.inductionOn with
    | h φ =>
      obtain ⟨φ', hφ'⟩ := extend_cocycle_across_trivial_factor M Q hM.1 hQ.1 hMQ hact φ
      refine ⟨Quotient.mk _ φ', ?_⟩
      change Quotient.mk _ (restrictCocycle le_top φ') = Quotient.mk _ φ
      rw [hφ']

end Numbered
end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1 u_2

theorem solution :
∀ {J : Type u_1} {N : Type u_2} [inst : Group.{u_1} J] [inst_1 : Group.{u_2} N] [inst_2 : TopologicalSpace.{u_1} J]
  [inst_3 : TopologicalSpace.{u_2} N]
  [inst_4 :
    @MulDistribMulAction.{u_1, u_2} J N (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
      (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} J inst inst_2] [@DiscreteTopology.{u_2} N inst_3]
  [Finite.{u_2 + 1} N]
  [@ContinuousSMul.{u_1, u_2} J N
      (@SemigroupAction.toSMul.{u_1, u_2} J N
        (@Monoid.toSemigroup.{u_1} J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst)))
        (@MulAction.toSemigroupAction.{u_1, u_2} J N
          (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
          (@MulDistribMulAction.toMulAction.{u_1, u_2} J N
            (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
            (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_4)))
      inst_2 inst_3]
  (p : Nat) (hp : Nat.Prime p) (hN : @IsPGroup.{u_2} p N inst_1)
  (hG :
    @LocalConjugacy.Proof.LocalConjugacy.Prosupersolvable.{max u_2 u_1}
      (@LocalConjugacy.Proof.LocalConjugacy.ActionProduct.{u_1, u_2} J N inst inst_1 inst_4)
      (@SemidirectProduct.instGroup.{u_2, u_1} N J inst_1 inst
        (@MulDistribMulAction.toMulAut.{u_1, u_2} J N inst
          (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_4))
      (@LocalConjugacy.Proof.LocalConjugacy.semidirectTopology.{u_1, u_2} J N inst inst_1 inst_2 inst_3
        (@MulDistribMulAction.toMulAut.{u_1, u_2} J N inst
          (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_4)))
  (Q : @Subgroup.{u_1} J inst)
  (hQ :
    @LocalConjugacy.Proof.LocalConjugacy.IsHallPro.{u_1} J inst inst_2
      (@Set.ofPred.{0} Nat fun (r : Nat) => @LE.le.{0} Nat instLENat r p) Q),
  @Function.Bijective.{max (u_2 + 1) (u_1 + 1), max (u_2 + 1) (u_1 + 1)}
    (@LocalConjugacy.Proof.LocalConjugacy.H1.{u_1, u_2} J N inst inst_1 inst_2 inst_3 inst_4
      (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)))
    (@LocalConjugacy.Proof.LocalConjugacy.H1.{u_1, u_2} J N inst inst_1 inst_2 inst_3 inst_4 Q)
    (@LocalConjugacy.Proof.LocalConjugacy.restrictH1.{u_1, u_2} J N inst inst_1 inst_2 inst_3 inst_4 Q
      (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst))
      (have this :
        @LE.le.{u_1} (@Subgroup.{u_1} J inst)
          (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
            (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
          Q (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)) :=
        @le_top.{u_1} (@Subgroup.{u_1} J inst)
          (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
            (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
          (@BoundedOrder.toOrderTop.{u_1} (@Subgroup.{u_1} J inst)
            (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
              (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
            (@CompleteLattice.toBoundedOrder.{u_1} (@Subgroup.{u_1} J inst)
              (@Subgroup.instCompleteLattice.{u_1} J inst)))
          Q;
      this)) :=
  @LocalConjugacy.Proof.LocalConjugacy.proposition_2_3_preparedProof
