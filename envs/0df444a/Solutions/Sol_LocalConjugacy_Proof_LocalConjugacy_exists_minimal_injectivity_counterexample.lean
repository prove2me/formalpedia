-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.exists_minimal_injectivity_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T17:05:00.152995+00:00
-- url     : https://prove2.me/submissions/aaae32ad-29b2-487f-84b7-12c5a52410fd

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
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_cohomologous_on_chain_intersection
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_exists_minimal_closed_subgroup_of_chain_condition

/-! Kernel-checked proof and its local helpers, retaining their original scopes. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

section Compactness
variable {J : Type*} [Group J] [TopologicalSpace J] [CompactSpace J]





end Compactness

section Extension
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [TopologicalSpace N] [MulDistribMulAction J N]







end Extension

section Obstructions
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [DiscreteTopology N]
  [MulDistribMulAction J N] [ContinuousSMul J N]



/-- Zorn supplies an inclusion-minimal closed intermediate subgroup on which a fixed
failure of injectivity persists. Minimality concerns this pair of cocycles. -/
private theorem exists_minimal_injectivity_counterexample_preparedProof
    (P : Subgroup J) (f g : Cocycle (N := N) (⊤ : Subgroup J))
    (hP : Cohomologous (restrictCocycle (show P ≤ ⊤ from le_top) f)
      (restrictCocycle le_top g)) (hbad : ¬ Cohomologous f g) :
    ∃ L : Subgroup J, IsClosed (L : Set J) ∧ P < L ∧
      ¬ Cohomologous (restrictCocycle (show L ≤ ⊤ from le_top) f)
        (restrictCocycle le_top g) ∧
      ∀ K : Subgroup J, IsClosed (K : Set J) → P ≤ K → K < L →
        Cohomologous (restrictCocycle (show K ≤ ⊤ from le_top) f)
          (restrictCocycle le_top g) := by
  classical
  let bad : Subgroup J → Prop := fun H =>
    ¬ Cohomologous (restrictCocycle (show H ≤ ⊤ from le_top) f) (restrictCocycle le_top g)
  have hb : bad ⊤ := hbad
  obtain ⟨L, hL⟩ := exists_minimal_closed_subgroup_of_chain_condition P bad hb (by
    intro c hn hc hh hgood
    obtain ⟨H, hH, hfg⟩ := cohomologous_on_chain_intersection f g c hn hc
      (fun H hH => (hh H hH).1) hgood
    exact (hh H hH).2.2 hfg)
  refine ⟨L, hL.1.1, lt_of_le_of_ne hL.1.2.1 ?_, hL.1.2.2, ?_⟩
  · intro he
    exact hL.1.2.2 (he ▸ hP)
  · intro K hK hPK hKL
    by_contra hfg
    exact hL.not_prop_of_lt hKL ⟨hK, hPK, hfg⟩











end Obstructions

section Invariance
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [IsTopologicalGroup J] [TopologicalSpace N]
  [MulDistribMulAction J N] [ContinuousSMul J N]



end Invariance
end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1 u_2

theorem solution :
∀ {J : Type u_1} {N : Type u_2} [inst : Group.{u_1} J] [inst_1 : Group.{u_2} N] [inst_2 : TopologicalSpace.{u_1} J]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} J inst inst_2] [inst_4 : TopologicalSpace.{u_2} N]
  [@DiscreteTopology.{u_2} N inst_4]
  [inst_6 :
    @MulDistribMulAction.{u_1, u_2} J N (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
      (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))]
  [@ContinuousSMul.{u_1, u_2} J N
      (@SemigroupAction.toSMul.{u_1, u_2} J N
        (@Monoid.toSemigroup.{u_1} J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst)))
        (@MulAction.toSemigroupAction.{u_1, u_2} J N
          (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
          (@MulDistribMulAction.toMulAction.{u_1, u_2} J N
            (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
            (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_6)))
      inst_2 inst_4]
  (P : @Subgroup.{u_1} J inst)
  (f g :
    @LocalConjugacy.Proof.LocalConjugacy.Cocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6
      (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)))
  (hP :
    @LocalConjugacy.Proof.LocalConjugacy.Cohomologous.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 P
      (@LocalConjugacy.Proof.LocalConjugacy.restrictCocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 P
        (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst))
        (have this :
          @LE.le.{u_1} (@Subgroup.{u_1} J inst)
            (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
              (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
            P (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)) :=
          @le_top.{u_1} (@Subgroup.{u_1} J inst)
            (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
              (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
            (@BoundedOrder.toOrderTop.{u_1} (@Subgroup.{u_1} J inst)
              (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
              (@CompleteLattice.toBoundedOrder.{u_1} (@Subgroup.{u_1} J inst)
                (@Subgroup.instCompleteLattice.{u_1} J inst)))
            P;
        this)
        f)
      (@LocalConjugacy.Proof.LocalConjugacy.restrictCocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 P
        (@Top.top.{u_1} (@Subgroup.{u_1} J inst)
          (@OrderTop.toTop.{u_1} (@Subgroup.{u_1} J inst)
            (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
              (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
            (@BoundedOrder.toOrderTop.{u_1} (@Subgroup.{u_1} J inst)
              (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
              (@CompleteLattice.toBoundedOrder.{u_1} (@Subgroup.{u_1} J inst)
                (@Subgroup.instCompleteLattice.{u_1} J inst)))))
        (@le_top.{u_1} (@Subgroup.{u_1} J inst)
          (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
            (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
          (@BoundedOrder.toOrderTop.{u_1} (@Subgroup.{u_1} J inst)
            (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
              (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
            (@CompleteLattice.toBoundedOrder.{u_1} (@Subgroup.{u_1} J inst)
              (@Subgroup.instCompleteLattice.{u_1} J inst)))
          P)
        g))
  (hbad :
    Not
      (@LocalConjugacy.Proof.LocalConjugacy.Cohomologous.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6
        (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)) f g)),
  @Exists.{u_1 + 1} (@Subgroup.{u_1} J inst) fun (L : @Subgroup.{u_1} J inst) =>
    And
      (@IsClosed.{u_1} J inst_2
        (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst) L))
      (And
        (@LT.lt.{u_1} (@Subgroup.{u_1} J inst)
          (@Preorder.toLT.{u_1} (@Subgroup.{u_1} J inst)
            (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
          P L)
        (And
          (Not
            (@LocalConjugacy.Proof.LocalConjugacy.Cohomologous.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 L
              (@LocalConjugacy.Proof.LocalConjugacy.restrictCocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 L
                (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst))
                (have this :
                  @LE.le.{u_1} (@Subgroup.{u_1} J inst)
                    (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                      (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst)
                        (@Subgroup.instPartialOrder.{u_1} J inst)))
                    L (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)) :=
                  @le_top.{u_1} (@Subgroup.{u_1} J inst)
                    (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                      (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst)
                        (@Subgroup.instPartialOrder.{u_1} J inst)))
                    (@BoundedOrder.toOrderTop.{u_1} (@Subgroup.{u_1} J inst)
                      (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                        (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst)
                          (@Subgroup.instPartialOrder.{u_1} J inst)))
                      (@CompleteLattice.toBoundedOrder.{u_1} (@Subgroup.{u_1} J inst)
                        (@Subgroup.instCompleteLattice.{u_1} J inst)))
                    L;
                this)
                f)
              (@LocalConjugacy.Proof.LocalConjugacy.restrictCocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 L
                (@Top.top.{u_1} (@Subgroup.{u_1} J inst)
                  (@OrderTop.toTop.{u_1} (@Subgroup.{u_1} J inst)
                    (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                      (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst)
                        (@Subgroup.instPartialOrder.{u_1} J inst)))
                    (@BoundedOrder.toOrderTop.{u_1} (@Subgroup.{u_1} J inst)
                      (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                        (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst)
                          (@Subgroup.instPartialOrder.{u_1} J inst)))
                      (@CompleteLattice.toBoundedOrder.{u_1} (@Subgroup.{u_1} J inst)
                        (@Subgroup.instCompleteLattice.{u_1} J inst)))))
                (@le_top.{u_1} (@Subgroup.{u_1} J inst)
                  (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                    (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
                  (@BoundedOrder.toOrderTop.{u_1} (@Subgroup.{u_1} J inst)
                    (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                      (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst)
                        (@Subgroup.instPartialOrder.{u_1} J inst)))
                    (@CompleteLattice.toBoundedOrder.{u_1} (@Subgroup.{u_1} J inst)
                      (@Subgroup.instCompleteLattice.{u_1} J inst)))
                  L)
                g)))
          (∀ (K : @Subgroup.{u_1} J inst),
            @IsClosed.{u_1} J inst_2
                (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst) K) →
              @LE.le.{u_1} (@Subgroup.{u_1} J inst)
                  (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                    (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
                  P K →
                @LT.lt.{u_1} (@Subgroup.{u_1} J inst)
                    (@Preorder.toLT.{u_1} (@Subgroup.{u_1} J inst)
                      (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst)
                        (@Subgroup.instPartialOrder.{u_1} J inst)))
                    K L →
                  @LocalConjugacy.Proof.LocalConjugacy.Cohomologous.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 K
                    (@LocalConjugacy.Proof.LocalConjugacy.restrictCocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4
                      inst_6 K (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst))
                      (have this :
                        @LE.le.{u_1} (@Subgroup.{u_1} J inst)
                          (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                            (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst)
                              (@Subgroup.instPartialOrder.{u_1} J inst)))
                          K (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)) :=
                        @le_top.{u_1} (@Subgroup.{u_1} J inst)
                          (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                            (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst)
                              (@Subgroup.instPartialOrder.{u_1} J inst)))
                          (@BoundedOrder.toOrderTop.{u_1} (@Subgroup.{u_1} J inst)
                            (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                              (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst)
                                (@Subgroup.instPartialOrder.{u_1} J inst)))
                            (@CompleteLattice.toBoundedOrder.{u_1} (@Subgroup.{u_1} J inst)
                              (@Subgroup.instCompleteLattice.{u_1} J inst)))
                          K;
                      this)
                      f)
                    (@LocalConjugacy.Proof.LocalConjugacy.restrictCocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4
                      inst_6 K
                      (@Top.top.{u_1} (@Subgroup.{u_1} J inst)
                        (@OrderTop.toTop.{u_1} (@Subgroup.{u_1} J inst)
                          (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                            (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst)
                              (@Subgroup.instPartialOrder.{u_1} J inst)))
                          (@BoundedOrder.toOrderTop.{u_1} (@Subgroup.{u_1} J inst)
                            (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                              (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst)
                                (@Subgroup.instPartialOrder.{u_1} J inst)))
                            (@CompleteLattice.toBoundedOrder.{u_1} (@Subgroup.{u_1} J inst)
                              (@Subgroup.instCompleteLattice.{u_1} J inst)))))
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
                        K)
                      g)))) :=
  @LocalConjugacy.Proof.LocalConjugacy.exists_minimal_injectivity_counterexample_preparedProof
