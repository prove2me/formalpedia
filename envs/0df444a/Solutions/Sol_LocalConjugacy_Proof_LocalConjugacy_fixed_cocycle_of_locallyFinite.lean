-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.fixed_cocycle_of_locallyFinite
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T16:59:59.716982+00:00
-- url     : https://prove2.me/submissions/071c6d7c-5698-4129-aaa8-f1163fd0207e

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
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_classAction_closed_stabilizers
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_cocycleInvarianceSubgroup_isClosed
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_exists_finite_invariant_coefficient_subgroup
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_proP_fixed_point

/-! Kernel-checked proof and its local helpers, retaining their original scopes. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [IsTopologicalGroup J] [TopologicalSpace N] [IsTopologicalGroup N]
  [MulDistribMulAction J N] [ContinuousSMul J N]













private theorem card_cohomologyClass {p : ℕ} [Fact p.Prime] (hN : IsPGroup p N)
    {K : Subgroup J} (f : Cocycle (N := N) K) [Finite (CohomologyClass f)] :
    ∃ k : ℕ, Nat.card (CohomologyClass f) = p ^ k := by
  letI := coefficientAction (N := N) K
  have he := Equiv.setCongr (orbit_eq_cohomologyClass f)
  letI : Finite (MulAction.orbit N f) := Finite.of_equiv (CohomologyClass f) he.symm
  obtain ⟨k, hk⟩ := hN.card_orbit f
  exact ⟨k, (Nat.card_congr he).symm.trans hk⟩









/-- The finite-orbit part of Proposition 2.1. It permits infinite `N` when
the particular cohomology class has finitely many representatives. -/
private theorem fixed_cocycle_of_finite_class [T2Space N]
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : q ≠ p) (hN : IsPGroup p N)
    {K : Subgroup J} [K.Normal] (Q : Subgroup J) (hQ : IsProP q Q)
    (f : Cocycle (N := N) K) (hinv : InvariantUnder Q K f)
    [Finite (CohomologyClass f)] :
    ∃ g : Cocycle (N := N) K, Cohomologous f g ∧
      ∀ x : Q, twistCocycle g x = g := by
  letI := classAction f Q hinv
  obtain ⟨k, hk⟩ := card_cohomologyClass hN f
  have hn : ¬ q ∣ Nat.card (CohomologyClass f) := by
    rw [hk]
    exact fun h => hpq ((Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime) (Fact.out : p.Prime)).mp
      ((Fact.out : q.Prime).dvd_of_dvd_pow h))
  obtain ⟨g, hg⟩ := proP_fixed_point hQ (classAction_closed_stabilizers f Q hinv) hn
  exact ⟨g.val, g.property, fun x => congrArg Subtype.val (hg x)⟩

end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy



section
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [CompactSpace J] [TopologicalSpace N] [DiscreteTopology N]
  [MulDistribMulAction J N] [ContinuousSMul J N]



end

section Subgroup
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [TopologicalSpace N]
  [MulDistribMulAction J N]
  (M : Subgroup N) (hM : ∀ (j : J) (n : N), n ∈ M → j • n ∈ M)



private theorem coefficientSubgroupContinuousSMul [ContinuousSMul J N] :
    letI := coefficientSubgroupAction M hM
    ContinuousSMul J M := by
  letI := coefficientSubgroupAction M hM
  exact ⟨(continuous_fst.smul (continuous_subtype_val.comp continuous_snd)).subtype_mk _⟩

namespace Cocycle



end Cocycle
end Subgroup

end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [IsTopologicalGroup J]
  [TopologicalSpace N] [IsTopologicalGroup N]
  [MulDistribMulAction J N] [ContinuousSMul J N]
  {K : Subgroup J} [K.Normal]





/-- Invariance under a dense cyclic subgroup suffices for a finite coefficient group. -/
private theorem invariantUnder_of_dense_generator [Finite N] [T2Space N]
    (Q : Subgroup J) (t : Q) (ht : Dense (Subgroup.zpowers t : Set Q))
    (f : Cocycle (N := N) K) (hf : Cohomologous f (twistCocycle f t)) :
    InvariantUnder Q K f := by
  let L := (cocycleInvarianceSubgroup f).comap Q.subtype
  have hL : IsClosed (L : Set Q) :=
    (cocycleInvarianceSubgroup_isClosed f).preimage continuous_subtype_val
  have hz : (Subgroup.zpowers t : Set Q) ⊆ L := Subgroup.zpowers_le.mpr hf
  have hall := closure_minimal hz hL
  rw [ht.closure_eq] at hall
  intro q hq
  have hq' : Cohomologous f (twistCocycle f q) := hall (Set.mem_univ (⟨q, hq⟩ : Q))
  obtain ⟨n, hn⟩ := hq'
  exact ⟨n, fun x hx _ => hn ⟨x, hx⟩⟩

end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

section
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [IsTopologicalGroup N]
  [DiscreteTopology N] [MulDistribMulAction J N] [ContinuousSMul J N]

/-- The finite orbit argument applies in a finite invariant coefficient subgroup,
even when the whole coefficient group and the whole cohomology class are infinite. -/
private theorem fixed_cocycle_of_locallyFinite_preparedProof
    (hfinite : LocallyFiniteGroup N)
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hne : q ≠ p) (hN : IsPGroup p N)
    {K : Subgroup J} [K.Normal] (hK : IsClosed (K : Set J))
    (Q : Subgroup J) (hcyclic : Procyclic Q) (hQ : IsProP q Q)
    (f : Cocycle (N := N) K) (hinv : InvariantUnder Q K f) :
    ∃ g : Cocycle (N := N) K, Cohomologous f g ∧
      ∀ x : Q, twistCocycle g x = g := by
  letI : Profinite K := profinite_closed_subgroup K hK
  obtain ⟨t, ht⟩ := hcyclic
  obtain ⟨n, hn⟩ := hinv t t.property
  obtain ⟨M, hMf, hMs, hMa⟩ := exists_finite_invariant_coefficient_subgroup
    (J := J) hfinite (Set.range f.toFun ∪ {n})
    ((isCompact_range f.continuous_toFun).finite_of_discrete.union (Set.finite_singleton n))
  letI : Finite M := hMf
  letI := coefficientSubgroupAction M hMa
  letI : ContinuousSMul J M := coefficientSubgroupContinuousSMul M hMa
  have hfM (x : K) : f.toFun x ∈ M := hMs (Or.inl ⟨x, rfl⟩)
  have hnM : n ∈ M := hMs (Or.inr rfl)
  let F := f.corestrictCoefficient M hMa hfM
  have hFt : Cohomologous F (twistCocycle F t) := by
    refine ⟨⟨n, hnM⟩, fun x => Subtype.ext ?_⟩
    exact hn x x.property (conjugateDomain K t x).property
  have hFi := invariantUnder_of_dense_generator Q t ht F hFt
  obtain ⟨g, hFg, hg⟩ := fixed_cocycle_of_finite_class hne
    (hN.to_subgroup M) Q hQ F hFi
  let G := g.mapCoefficient M.subtype continuous_subtype_val (fun _ _ => rfl)
  refine ⟨G, ?_, ?_⟩
  · obtain ⟨m, hm⟩ := hFg
    exact ⟨m.val, fun x => congrArg Subtype.val (hm x)⟩
  · intro x
    apply Cocycle.ext
    intro y
    exact congrArg (fun c : Cocycle (N := M) K => (c.toFun y).val) (hg x)





end

section Statements
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [TopologicalSpace N] [MulDistribMulAction J N]





end Statements
end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1 u_2

theorem solution :
∀ {J : Type u_1} {N : Type u_2} [inst : Group.{u_1} J] [inst_1 : Group.{u_2} N] [inst_2 : TopologicalSpace.{u_1} J]
  [inst_3 : @LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} J inst inst_2] [inst_4 : TopologicalSpace.{u_2} N]
  [@IsTopologicalGroup.{u_2} N inst_4 inst_1] [@DiscreteTopology.{u_2} N inst_4]
  [inst_7 :
    @MulDistribMulAction.{u_1, u_2} J N (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
      (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))]
  [inst_8 :
    @ContinuousSMul.{u_1, u_2} J N
      (@SemigroupAction.toSMul.{u_1, u_2} J N
        (@Monoid.toSemigroup.{u_1} J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst)))
        (@MulAction.toSemigroupAction.{u_1, u_2} J N
          (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
          (@MulDistribMulAction.toMulAction.{u_1, u_2} J N
            (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
            (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_7)))
      inst_2 inst_4]
  (hfinite : @LocalConjugacy.Proof.LocalConjugacy.LocallyFiniteGroup.{u_2} N inst_1) {p q : Nat} [Fact (Nat.Prime p)]
  [Fact (Nat.Prime q)] (hne : @Ne.{1} Nat q p) (hN : @IsPGroup.{u_2} p N inst_1) {K : @Subgroup.{u_1} J inst}
  [inst_11 : @Subgroup.Normal.{u_1} J inst K]
  (hK :
    @IsClosed.{u_1} J inst_2
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst) K))
  (Q : @Subgroup.{u_1} J inst)
  (hcyclic :
    @LocalConjugacy.Proof.LocalConjugacy.Procyclic.{u_1}
      (@Subtype.{u_1 + 1} J fun (x : J) =>
        @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) Q x)
      (@Subgroup.toGroup.{u_1} J inst Q)
      (@instTopologicalSpaceSubtype.{u_1} J
        (fun (x : J) =>
          @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) Q x)
        inst_2))
  (hQ :
    @LocalConjugacy.Proof.LocalConjugacy.IsProP.{u_1} q
      (@Subtype.{u_1 + 1} J fun (x : J) =>
        @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) Q x)
      (@Subgroup.toGroup.{u_1} J inst Q)
      (@instTopologicalSpaceSubtype.{u_1} J
        (fun (x : J) =>
          @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) Q x)
        inst_2))
  (f : @LocalConjugacy.Proof.LocalConjugacy.Cocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_7 K)
  (hinv : @LocalConjugacy.Proof.LocalConjugacy.InvariantUnder.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_7 Q K f),
  @Exists.{max (u_1 + 1) (u_2 + 1)}
    (@LocalConjugacy.Proof.LocalConjugacy.Cocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_7 K)
    fun (g : @LocalConjugacy.Proof.LocalConjugacy.Cocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_7 K) =>
    And (@LocalConjugacy.Proof.LocalConjugacy.Cohomologous.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_7 K f g)
      (∀
        (x :
          @Subtype.{u_1 + 1} J fun (x : J) =>
            @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) Q x),
        @Eq.{max (u_1 + 1) (u_2 + 1)}
          (@LocalConjugacy.Proof.LocalConjugacy.Cocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_7 K)
          (@LocalConjugacy.Proof.LocalConjugacy.twistCocycle.{u_1, u_2} J N inst inst_1 inst_2
            (@LocalConjugacy.Proof.LocalConjugacy.Profinite.toIsTopologicalGroup.{u_1} J inst inst_2 inst_3) inst_4
            inst_7 inst_8 K inst_11 g
            (@Subtype.val.{u_1 + 1} J
              (fun (x : J) =>
                @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) Q
                  x)
              x))
          g) :=
  @LocalConjugacy.Proof.LocalConjugacy.fixed_cocycle_of_locallyFinite_preparedProof
