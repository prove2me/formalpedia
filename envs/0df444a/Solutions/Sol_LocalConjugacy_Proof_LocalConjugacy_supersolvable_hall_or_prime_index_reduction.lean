-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.supersolvable_hall_or_prime_index_reduction
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T17:41:39.609351+00:00
-- url     : https://prove2.me/submissions/5bc00f07-77e1-4530-825b-f74ecbe465fe

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
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_hall_complement_restriction
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_prosupersolvable_action_trivial_on_high_primes
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_prosupersolvable_hall_split_containing
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_prosupersolvable_prime_index_above_normal_sylow
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_subgroup_quotient_factors
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_sylowPro_normal_of_prosupersolvable_largest

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









private theorem hall_complement_proper {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]
    {p : ℕ} {Q : Subgroup G} (hQ : IsHallPro {r | r ≤ p} Q)
    (hlarge : ∃ (U : OpenNormalSubgroup G) (q : ℕ), q.Prime ∧
      q ∣ Nat.card (G ⧸ U.toSubgroup) ∧ p < q) : Q ≠ ⊤ := by
  intro he
  obtain ⟨U, q, hq, hd, hpq⟩ := hlarge
  have hh := (hQ.2 U).1
  rw [he, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective U.toSubgroup)] at hh
  have hle := hh q hq (by simpa only [Subgroup.card_top] using hd)
  exact Nat.not_lt_of_ge hle hpq

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



/-- The two structural reductions needed by Zorn, with all Hall and
centralization facts derived from prosupersolvability of the semidirect product. -/
private theorem supersolvable_hall_or_prime_index_reduction_preparedProof
    (hG : Prosupersolvable (ActionProduct J N)) {p : ℕ} [Fact p.Prime]
    (hN : IsPGroup p N) (P : Subgroup J) (hP : IsSylowPro p ⊤ P) (hproper : P ≠ ⊤) :
    (∃ M Q : Subgroup J, M.Normal ∧ IsHallPro {r | p < r} M ∧
      IsHallPro {r | r ≤ p} Q ∧ M.IsComplement' Q ∧ P ≤ Q ∧ Q < ⊤ ∧
      RestrictionIsomorphism (N := N) ⊤ Q le_top) ∨
    (P.Normal ∧ ∃ K : OpenNormalSubgroup J, P ≤ K.toSubgroup ∧
      K.toSubgroup.index.Prime ∧ K.toSubgroup.index ≠ p) := by
  classical
  have hJ := prosupersolvable_acting_group hG
  by_cases hlarge : ∃ (U : OpenNormalSubgroup J) (q : ℕ), q.Prime ∧
      q ∣ Nat.card (J ⧸ U.toSubgroup) ∧ p < q
  · obtain ⟨M, Q, hMn, hM, hQ, hMQ, hPQ⟩ :=
      prosupersolvable_hall_split_containing hJ le_rfl P hP
    letI := hMn
    have hact := prosupersolvable_action_trivial_on_high_primes hG hN M hM.hasProPrimes
    exact Or.inl ⟨M, Q, hMn, hM, hQ, hMQ, hPQ, lt_top_iff_ne_top.mpr
      (hall_complement_proper hQ hlarge),
      hall_complement_restriction hN M Q hM.1 hQ.1 hMQ hM.hasProPrimes hact⟩
  · have hprimes (U : OpenNormalSubgroup J) : HasPrimes {r | r ≤ p} (J ⧸ U.toSubgroup) := by
      intro q hq hd
      exact Nat.le_of_not_gt (fun hpq => hlarge ⟨U, q, hq, hd, hpq⟩)
    have hn := sylowPro_normal_of_prosupersolvable_largest hJ hprimes P hP
    letI := hn
    exact Or.inr ⟨hn, prosupersolvable_prime_index_above_normal_sylow hJ P hP hproper⟩

end Action
end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1 u_2

theorem solution :
∀ {J : Type u_1} {N : Type u_2} [inst : Group.{u_1} J] [inst_1 : Group.{u_2} N] [inst_2 : TopologicalSpace.{u_1} J]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} J inst inst_2] [inst_4 : TopologicalSpace.{u_2} N]
  [@DiscreteTopology.{u_2} N inst_4] [Finite.{u_2 + 1} N]
  [inst_7 :
    @MulDistribMulAction.{u_1, u_2} J N (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
      (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))]
  [@ContinuousSMul.{u_1, u_2} J N
      (@SemigroupAction.toSMul.{u_1, u_2} J N
        (@Monoid.toSemigroup.{u_1} J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst)))
        (@MulAction.toSemigroupAction.{u_1, u_2} J N
          (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
          (@MulDistribMulAction.toMulAction.{u_1, u_2} J N
            (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
            (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_7)))
      inst_2 inst_4]
  (hG :
    @LocalConjugacy.Proof.LocalConjugacy.Prosupersolvable.{max u_2 u_1}
      (@LocalConjugacy.Proof.LocalConjugacy.ActionProduct.{u_1, u_2} J N inst inst_1 inst_7)
      (@SemidirectProduct.instGroup.{u_2, u_1} N J inst_1 inst
        (@MulDistribMulAction.toMulAut.{u_1, u_2} J N inst
          (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_7))
      (@LocalConjugacy.Proof.LocalConjugacy.semidirectTopology.{u_1, u_2} J N inst inst_1 inst_2 inst_4
        (@MulDistribMulAction.toMulAut.{u_1, u_2} J N inst
          (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_7)))
  {p : Nat} [Fact (Nat.Prime p)] (hN : @IsPGroup.{u_2} p N inst_1) (P : @Subgroup.{u_1} J inst)
  (hP :
    @LocalConjugacy.Proof.LocalConjugacy.IsSylowPro.{u_1} p J inst inst_2
      (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)) P)
  (hproper :
    @Ne.{u_1 + 1} (@Subgroup.{u_1} J inst) P
      (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst))),
  Or
    (@Exists.{u_1 + 1} (@Subgroup.{u_1} J inst) fun (M : @Subgroup.{u_1} J inst) =>
      @Exists.{u_1 + 1} (@Subgroup.{u_1} J inst) fun (Q : @Subgroup.{u_1} J inst) =>
        And (@Subgroup.Normal.{u_1} J inst M)
          (And
            (@LocalConjugacy.Proof.LocalConjugacy.IsHallPro.{u_1} J inst inst_2
              (@Set.ofPred.{0} Nat fun (r : Nat) => @LT.lt.{0} Nat instLTNat p r) M)
            (And
              (@LocalConjugacy.Proof.LocalConjugacy.IsHallPro.{u_1} J inst inst_2
                (@Set.ofPred.{0} Nat fun (r : Nat) => @LE.le.{0} Nat instLENat r p) Q)
              (And (@Subgroup.IsComplement'.{u_1} J inst M Q)
                (And
                  (@LE.le.{u_1} (@Subgroup.{u_1} J inst)
                    (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                      (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst)
                        (@Subgroup.instPartialOrder.{u_1} J inst)))
                    P Q)
                  (And
                    (@LT.lt.{u_1} (@Subgroup.{u_1} J inst)
                      (@Preorder.toLT.{u_1} (@Subgroup.{u_1} J inst)
                        (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst)
                          (@Subgroup.instPartialOrder.{u_1} J inst)))
                      Q (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)))
                    (@LocalConjugacy.Proof.LocalConjugacy.RestrictionIsomorphism.{u_1, u_2} J N inst inst_1 inst_2
                      inst_4 inst_7 (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)) Q
                      (@le_top.{u_1} (@Subgroup.{u_1} J inst)
                        (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                          (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst)
                            (@Subgroup.instPartialOrder.{u_1} J inst)))
                        (@BoundedOrder.toOrderTop.{u_1} (@Subgroup.{u_1} J inst)
                          (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                            (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst)
                              (@Subgroup.instPartialOrder.{u_1} J inst)))
                          (@CompleteLattice.toBoundedOrder.{u_1} (@Subgroup.{u_1} J inst)
                            (@Subgroup.instCompleteLattice.{u_1} J inst)))
                        Q))))))))
    (And (@Subgroup.Normal.{u_1} J inst P)
      (@Exists.{u_1 + 1} (@OpenNormalSubgroup.{u_1} J inst inst_2) fun (K : @OpenNormalSubgroup.{u_1} J inst inst_2) =>
        And
          (@LE.le.{u_1} (@Subgroup.{u_1} J inst)
            (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
              (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
            P (@OpenSubgroup.toSubgroup.{u_1} J inst inst_2 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} J inst inst_2 K)))
          (And
            (Nat.Prime
              (@Subgroup.index.{u_1} J inst
                (@OpenSubgroup.toSubgroup.{u_1} J inst inst_2
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} J inst inst_2 K))))
            (@Ne.{1} Nat
              (@Subgroup.index.{u_1} J inst
                (@OpenSubgroup.toSubgroup.{u_1} J inst inst_2
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} J inst inst_2 K)))
              p)))) :=
  @LocalConjugacy.Proof.LocalConjugacy.supersolvable_hall_or_prime_index_reduction_preparedProof
