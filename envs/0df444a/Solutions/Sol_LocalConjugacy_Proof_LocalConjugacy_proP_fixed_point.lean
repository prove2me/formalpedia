-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.proP_fixed_point
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T16:43:35.31999+00:00
-- url     : https://prove2.me/submissions/13512976-5df4-4f21-9563-36a48555b096

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

/-! Kernel-checked proof and its local helpers, retaining their original scopes. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

/-- A pro-`p` group acting on a finite set with closed stabilizers has a
fixed point whenever the cardinality of the set is prime to `p`. -/
private theorem proP_fixed_point_preparedProof {G Ω : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MulAction G Ω] [Finite Ω]
    {p : ℕ} [Fact p.Prime] (hG : IsProP p G)
    (hc : ∀ x : Ω, IsClosed (MulAction.stabilizer G x : Set G))
    (hcard : ¬ p ∣ Nat.card Ω) : ∃ x : Ω, ∀ g : G, g • x = x := by
  let ρ := MulAction.toPermHom G Ω
  have hk : IsClosed (ρ.ker : Set G) := by
    have he : (ρ.ker : Set G) = ⋂ x : Ω, (MulAction.stabilizer G x : Set G) := by
      ext g
      simp only [Set.mem_iInter, MulAction.mem_stabilizer_iff, MonoidHom.mem_ker]
      change ρ g = 1 ↔ ∀ x, g • x = x
      exact Equiv.ext_iff
    rw [he]
    exact isClosed_iInter hc
  let U : OpenNormalSubgroup G :=
    { toSubgroup := ρ.ker
      isOpen' := ρ.ker.isOpen_of_isClosed_of_finiteIndex hk }
  have hr : IsPGroup p ρ.range := (hG U).of_equiv (QuotientGroup.quotientKerEquivRange ρ)
  letI : MulAction ρ.range Ω := MulAction.compHom Ω ρ.range.subtype
  obtain ⟨x, hx⟩ := hr.nonempty_fixed_point_of_prime_not_dvd_card Ω hcard
  refine ⟨x, fun g => ?_⟩
  exact hx ⟨ρ g, ⟨g, rfl⟩⟩

end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1 u_2

theorem solution :
∀ {G : Type u_1} {Ω : Type u_2} [inst : Group.{u_1} G] [inst_1 : TopologicalSpace.{u_1} G]
  [@IsTopologicalGroup.{u_1} G inst_1 inst]
  [inst_3 : @MulAction.{u_1, u_2} G Ω (@DivInvMonoid.toMonoid.{u_1} G (@Group.toDivInvMonoid.{u_1} G inst))]
  [Finite.{u_2 + 1} Ω] {p : Nat} [Fact (Nat.Prime p)]
  (hG : @LocalConjugacy.Proof.LocalConjugacy.IsProP.{u_1} p G inst inst_1)
  (hc :
    ∀ (x : Ω),
      @IsClosed.{u_1} G inst_1
        (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)
          (@MulAction.stabilizer.{u_1, u_2} G Ω inst inst_3 x)))
  (hcard : Not (@Dvd.dvd.{0} Nat Nat.instDvd p (Nat.card.{u_2} Ω))),
  @Exists.{u_2 + 1} Ω fun (x : Ω) =>
    ∀ (g : G),
      @Eq.{u_2 + 1} Ω
        (@HSMul.hSMul.{u_1, u_2, u_2} G Ω Ω
          (@instHSMul.{u_1, u_2} G Ω
            (@SemigroupAction.toSMul.{u_1, u_2} G Ω
              (@Monoid.toSemigroup.{u_1} G (@DivInvMonoid.toMonoid.{u_1} G (@Group.toDivInvMonoid.{u_1} G inst)))
              (@MulAction.toSemigroupAction.{u_1, u_2} G Ω
                (@DivInvMonoid.toMonoid.{u_1} G (@Group.toDivInvMonoid.{u_1} G inst)) inst_3)))
          g x)
        x :=
  @LocalConjugacy.Proof.LocalConjugacy.proP_fixed_point_preparedProof
