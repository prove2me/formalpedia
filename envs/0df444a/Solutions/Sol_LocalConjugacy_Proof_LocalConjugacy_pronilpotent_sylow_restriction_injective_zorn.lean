-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.pronilpotent_sylow_restriction_injective_zorn
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T17:15:10.075977+00:00
-- url     : https://prove2.me/submissions/5fac68e0-613e-4cf4-9120-792b96b869d1

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
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_coprime_prime_index_restriction
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_exists_minimal_injectivity_counterexample
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_isSylowPro_subgroupOf
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_pronilpotent_prime_index_above_sylow
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_subgroup_quotient_factors

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









/-- The fixed-pair Zorn induction principle. A proof for an intermediate
subgroup may use cohomology of this pair on all smaller intermediate subgroups. -/
private theorem cohomologous_of_zorn_step
    (P : Subgroup J) (f g : Cocycle (N := N) (⊤ : Subgroup J))
    (hP : Cohomologous (restrictCocycle (show P ≤ ⊤ from le_top) f)
      (restrictCocycle le_top g))
    (step : ∀ L : Subgroup J, IsClosed (L : Set J) → P < L →
      (∀ K : Subgroup J, IsClosed (K : Set J) → P ≤ K → K < L →
        Cohomologous (restrictCocycle (show K ≤ ⊤ from le_top) f)
          (restrictCocycle le_top g)) →
      Cohomologous (restrictCocycle (show L ≤ ⊤ from le_top) f)
        (restrictCocycle le_top g)) : Cohomologous f g := by
  classical
  by_contra hbad
  obtain ⟨L, hL, hPL, hfg, hmin⟩ := exists_minimal_injectivity_counterexample P f g hP hbad
  exact hfg (step L hL hPL hmin)





end Obstructions

section Invariance
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [IsTopologicalGroup J] [TopologicalSpace N]
  [MulDistribMulAction J N] [ContinuousSMul J N]



end Invariance
end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

/-- A chosen Sylow subgroup remains Sylow in every intermediate subgroup. -/
private theorem isSylowPro_of_intermediate {J : Type*} [Group J] [TopologicalSpace J]
    {p : ℕ} {H L P : Subgroup J} (hP : IsSylowPro p H P)
    (hPL : P ≤ L) (hLH : L ≤ H) : IsSylowPro p L P :=
  ⟨hPL, hP.2.1, hP.2.2.1,
    fun Q hQL hQclosed hQpro hPQ => hP.2.2.2 Q (hQL.trans hLH) hQclosed hQpro hPQ⟩

variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [DiscreteTopology N]
  [MulDistribMulAction J N] [ContinuousSMul J N]





end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

section Intermediate
variable {J : Type*} [Group J] [TopologicalSpace J] [Profinite J]

private theorem closed_intermediate_image (P L : Subgroup J) (hL : IsClosed (L : Set J))
    (hPL : P ≤ L) (K : Subgroup L) (hK : IsClosed (K : Set L))
    (hPK : P.subgroupOf L ≤ K) (hproper : K < ⊤) :
    IsClosed (K.map L.subtype : Set J) ∧ P ≤ K.map L.subtype ∧ K.map L.subtype < L := by
  letI := profinite_closed_subgroup L hL
  refine ⟨(hK.isCompact.image continuous_subtype_val).isClosed, ?_, ?_⟩
  · simpa only [Subgroup.map_subgroupOf_eq_of_le hPL] using Subgroup.map_mono hPK (f := L.subtype)
  · refine lt_of_le_of_ne ((Subgroup.map_le_range L.subtype K).trans (le_of_eq L.range_subtype)) ?_
    intro he
    have he' : K.map L.subtype = (⊤ : Subgroup L).map L.subtype := by
      rw [← MonoidHom.range_eq_map, L.range_subtype, he]
    exact hproper.ne ((Subgroup.map_injective L.subtype_injective) he')

private theorem openNormal_lt_top_of_prime_index {L : Type*} [Group L] [TopologicalSpace L]
    (K : OpenNormalSubgroup L) (hq : K.toSubgroup.index.Prime) : K.toSubgroup < ⊤ := by
  apply lt_top_iff_ne_top.mpr
  intro he
  exact hq.ne_one (by rw [he, Subgroup.index_top])

end Intermediate

section Rebase
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [TopologicalSpace N] [MulDistribMulAction J N]







end Rebase

section Restriction
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [DiscreteTopology N] [Finite N]
  [MulDistribMulAction J N] [ContinuousSMul J N]







end Restriction
end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

/-! The pronilpotent branch of Lemma 1.2, using the manuscript's two Zorn
arguments: first a fixed pair of cocycles, then one stable class. -/

namespace LocalConjugacy

private theorem pronilpotent_subgroup {J : Type*} [Group J] [TopologicalSpace J] [Profinite J]
    (hJ : Pronilpotent J) (L : Subgroup J) : Pronilpotent L := by
  intro V
  obtain ⟨U, f, hf⟩ := subgroup_quotient_factors L V
  letI := hJ U
  exact Group.nilpotent_of_surjective f hf



variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [DiscreteTopology N] [Finite N]
  [MulDistribMulAction J N] [ContinuousSMul J N]

/-- Injectivity, by minimality for one inequivalent pair of cocycles. -/
private theorem pronilpotent_sylow_restriction_injective_zorn_preparedProof
    (hJ : Pronilpotent J) {p : ℕ} [Fact p.Prime]
    (hN : IsPGroup p N) (P : Subgroup J) (hP : IsSylowPro p ⊤ P)
    (φ ψ : Cocycle (N := N) (⊤ : Subgroup J))
    (hφψ : Cohomologous (restrictCocycle (show P ≤ ⊤ from le_top) φ)
      (restrictCocycle le_top ψ)) : Cohomologous φ ψ := by
  apply cohomologous_of_zorn_step P φ ψ hφψ
  intro L hL hPL hmin
  letI := profinite_closed_subgroup L hL
  have hJL := pronilpotent_subgroup hJ L
  have hPLs := isSylowPro_subgroupOf L P hL (isSylowPro_of_intermediate hP hPL.le le_top)
  have hproper : P.subgroupOf L ≠ ⊤ := by
    intro he
    have hh := congrArg (Subgroup.map L.subtype) he
    rw [Subgroup.map_subgroupOf_eq_of_le hPL.le, ← MonoidHom.range_eq_map, L.range_subtype] at hh
    exact hPL.ne hh
  obtain ⟨J₀, hPJ₀, hprime, hne⟩ :=
    pronilpotent_prime_index_above_sylow hJL (P.subgroupOf L) hPLs hproper
  letI : Fact J₀.toSubgroup.index.Prime := ⟨hprime⟩
  obtain ⟨hclosed, hle, hlt⟩ := closed_intermediate_image P L hL hPL.le
    J₀.toSubgroup J₀.isClosed hPJ₀ (openNormal_lt_top_of_prime_index J₀ hprime)
  obtain ⟨n, hn⟩ := hmin _ hclosed hle hlt
  have hsmall : Cohomologous
      (restrictCocycle (show J₀.toSubgroup ≤ ⊤ from le_top)
        (restrictCocycle (show L ≤ ⊤ from le_top) φ).subgroupTop)
      (restrictCocycle le_top (restrictCocycle le_top ψ).subgroupTop) :=
    ⟨n, fun x => hn ⟨x, Subgroup.mem_map_of_mem L.subtype x.property⟩⟩
  obtain ⟨m, hm⟩ := (coprime_prime_index_restriction hne hN J₀.toSubgroup
    J₀.isClosed rfl).1 (restrictCocycle (show L ≤ ⊤ from le_top) φ).subgroupTop
      (restrictCocycle (show L ≤ ⊤ from le_top) ψ).subgroupTop hsmall
  exact ⟨m, fun x => hm ⟨x, trivial⟩⟩



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
  (hJ : @LocalConjugacy.Proof.LocalConjugacy.Pronilpotent.{u_1} J inst inst_2) {p : Nat} [Fact (Nat.Prime p)]
  (hN : @IsPGroup.{u_2} p N inst_1) (P : @Subgroup.{u_1} J inst)
  (hP :
    @LocalConjugacy.Proof.LocalConjugacy.IsSylowPro.{u_1} p J inst inst_2
      (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)) P)
  (φ ψ :
    @LocalConjugacy.Proof.LocalConjugacy.Cocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_7
      (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)))
  (hφψ :
    @LocalConjugacy.Proof.LocalConjugacy.Cohomologous.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_7 P
      (@LocalConjugacy.Proof.LocalConjugacy.restrictCocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_7 P
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
        φ)
      (@LocalConjugacy.Proof.LocalConjugacy.restrictCocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_7 P
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
        ψ)),
  @LocalConjugacy.Proof.LocalConjugacy.Cohomologous.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_7
    (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)) φ ψ :=
  @LocalConjugacy.Proof.LocalConjugacy.pronilpotent_sylow_restriction_injective_zorn_preparedProof
