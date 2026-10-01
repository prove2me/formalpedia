-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.conjugate_le_full_sylow
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T16:38:32.850988+00:00
-- url     : https://prove2.me/submissions/6a8103c0-ba8f-40fa-b40d-863d3fbe485d

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
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_conjugate_le_of_finite_quotient_inclusions

/-! Kernel-checked proof and its local helpers, retaining their original scopes. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy



/-- A continuous homomorphism into a discrete group sends pro-`p` elements
to elements of finite `p`-power order. No finiteness of the codomain is needed. -/
private theorem image_pow {G F : Type*} [Group G] [Group F]
    [TopologicalSpace G] [TopologicalSpace F] [DiscreteTopology F]
    {p : ℕ} (h : IsProP p G) (f : G →* F) (hf : Continuous f) (x : G) :
    ∃ k : ℕ, f x ^ p ^ k = 1 := by
  let U : OpenNormalSubgroup G :=
    { toSubgroup := f.ker
      isOpen' := hf.isOpen_preimage _ (isOpen_discrete {1}) }
  obtain ⟨k, hk⟩ := h U (QuotientGroup.mk' U.toSubgroup x)
  refine ⟨k, ?_⟩
  have he := congrArg (QuotientGroup.lift U.toSubgroup f (by rfl)) hk
  simpa using he









end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

variable {G F : Type*} [Group G] [Group F]







private theorem conjugate_mono (g : G) {H K : Subgroup G} (h : H ≤ K) :
    conjugate g H ≤ conjugate g K := Subgroup.map_mono h





private theorem sylow_smul_toSubgroup (p : ℕ) (g : G) (P : Sylow p G) :
    (g • P).toSubgroup = conjugate g P.toSubgroup := by
  simp only [Sylow.smul_def, Sylow.pointwise_smul_def,
    Subgroup.pointwise_smul_def, conjugate]
  congr 1

end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

universe u
variable {G : Type u} [Group G] [TopologicalSpace G] [Profinite G]







private theorem isPGroup_quotient_image {p : ℕ} (H : Subgroup G) (hH : IsProP p H)
    (U : OpenNormalSubgroup G) : IsPGroup p (H.map (QuotientGroup.mk' U.toSubgroup)) := by
  let π := QuotientGroup.mk' U.toSubgroup
  let f : H →* G ⧸ U.toSubgroup := π.comp H.subtype
  have hf : Continuous f := continuous_quotient_mk'.comp continuous_subtype_val
  intro x
  obtain ⟨y, hy, he⟩ := x.property
  obtain ⟨k, hk⟩ := image_pow hH f hf ⟨y, hy⟩
  refine ⟨k, Subtype.ext ?_⟩
  change x.val ^ p ^ k = 1
  change π y ^ p ^ k = 1 at hk
  rwa [show π y = x.val from he] at hk



namespace FiniteSylowSystem
open CategoryTheory















variable {p : ℕ} [Fact p.Prime]
variable (P : (U : OpenNormalSubgroup G) → Sylow p (G ⧸ U.toSubgroup))
variable (hP : ∀ (U V : OpenNormalSubgroup G) (h : U ≤ V),
  (P U).mapSurjective (transition_surjective h) = P V)







include hP







end FiniteSylowSystem



/-- Every pro-`p` subgroup is conjugate into a subgroup having full Sylow
image in every finite quotient. -/
private theorem conjugate_le_full_sylow_preparedProof {p : ℕ} [Fact p.Prime] (H P : Subgroup G)
    (hH : IsProP p H) (hP : IsClosed (P : Set G))
    (hfull : ∀ U : OpenNormalSubgroup G, ∃ S : Sylow p (G ⧸ U.toSubgroup),
      P.map (QuotientGroup.mk' U.toSubgroup) = (S : Subgroup _)) :
    ∃ g : G, conjugate g H ≤ P := by
  apply conjugate_le_of_finite_quotient_inclusions H P hP
  intro U
  obtain ⟨S, hS⟩ := hfull U
  obtain ⟨T, hT⟩ := (isPGroup_quotient_image H hH U).exists_le_sylow
  obtain ⟨q, hq⟩ := MulAction.exists_smul_eq (G ⧸ U.toSubgroup) T S
  refine ⟨q, ?_⟩
  rw [hS]
  have he : conjugate q (T : Subgroup _) = (S : Subgroup _) := by
    have he := congrArg Sylow.toSubgroup hq
    simpa only [sylow_smul_toSubgroup] using he
  exact (conjugate_mono q hT).trans he.le

























end LocalConjugacy

end LocalConjugacy.Proof

end

universe u

theorem solution :
∀ {G : Type u} [inst : Group.{u} G] [inst_1 : TopologicalSpace.{u} G]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u} G inst inst_1] {p : Nat} [Fact (Nat.Prime p)]
  (H P : @Subgroup.{u} G inst)
  (hH :
    @LocalConjugacy.Proof.LocalConjugacy.IsProP.{u} p
      (@Subtype.{u + 1} G fun (x : G) =>
        @Membership.mem.{u, u} G (@Subgroup.{u} G inst)
          (@SetLike.instMembership.{u, u} (@Subgroup.{u} G inst) G (@Subgroup.instSetLike.{u} G inst)) H x)
      (@Subgroup.toGroup.{u} G inst H)
      (@instTopologicalSpaceSubtype.{u} G
        (fun (x : G) =>
          @Membership.mem.{u, u} G (@Subgroup.{u} G inst)
            (@SetLike.instMembership.{u, u} (@Subgroup.{u} G inst) G (@Subgroup.instSetLike.{u} G inst)) H x)
        inst_1))
  (hP : @IsClosed.{u} G inst_1 (@SetLike.coe.{u, u} (@Subgroup.{u} G inst) G (@Subgroup.instSetLike.{u} G inst) P))
  (hfull :
    ∀ (U : @OpenNormalSubgroup.{u} G inst inst_1),
      @Exists.{u + 1}
        (@Sylow.{u} p
          (@HasQuotient.Quotient.{u, u} G (@Subgroup.{u} G inst) (@QuotientGroup.instHasQuotientSubgroup.{u} G inst)
            (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U)))
          (@QuotientGroup.Quotient.group.{u} G inst
            (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U))
            (@OpenNormalSubgroup.instNormal.{u} G inst inst_1 U)))
        fun
          (S :
            @Sylow.{u} p
              (@HasQuotient.Quotient.{u, u} G (@Subgroup.{u} G inst) (@QuotientGroup.instHasQuotientSubgroup.{u} G inst)
                (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U)))
              (@QuotientGroup.Quotient.group.{u} G inst
                (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U))
                (@OpenNormalSubgroup.instNormal.{u} G inst inst_1 U))) =>
        @Eq.{u + 1}
          (@Subgroup.{u}
            (@HasQuotient.Quotient.{u, u} G (@Subgroup.{u} G inst) (@QuotientGroup.instHasQuotientSubgroup.{u} G inst)
              (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U)))
            (@QuotientGroup.Quotient.group.{u} G inst
              (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U))
              (@OpenNormalSubgroup.instNormal.{u} G inst inst_1 U)))
          (@Subgroup.map.{u, u} G inst
            (@HasQuotient.Quotient.{u, u} G (@Subgroup.{u} G inst) (@QuotientGroup.instHasQuotientSubgroup.{u} G inst)
              (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U)))
            (@QuotientGroup.Quotient.group.{u} G inst
              (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U))
              (@OpenNormalSubgroup.instNormal.{u} G inst inst_1 U))
            (@QuotientGroup.mk'.{u} G inst
              (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U))
              (@OpenNormalSubgroup.instNormal.{u} G inst inst_1 U))
            P)
          (@Sylow.toSubgroup.{u} p
            (@HasQuotient.Quotient.{u, u} G (@Subgroup.{u} G inst) (@QuotientGroup.instHasQuotientSubgroup.{u} G inst)
              (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U)))
            (@QuotientGroup.Quotient.group.{u} G inst
              (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U))
              (@OpenNormalSubgroup.instNormal.{u} G inst inst_1 U))
            S)),
  @Exists.{u + 1} G fun (g : G) =>
    @LE.le.{u} (@Subgroup.{u} G inst)
      (@Preorder.toLE.{u} (@Subgroup.{u} G inst)
        (@PartialOrder.toPreorder.{u} (@Subgroup.{u} G inst) (@Subgroup.instPartialOrder.{u} G inst)))
      (@LocalConjugacy.Proof.LocalConjugacy.conjugate.{u} G inst g H) P :=
  @LocalConjugacy.Proof.LocalConjugacy.conjugate_le_full_sylow_preparedProof
