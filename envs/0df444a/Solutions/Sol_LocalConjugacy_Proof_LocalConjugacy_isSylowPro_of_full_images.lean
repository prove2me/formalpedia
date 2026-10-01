-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.isSylowPro_of_full_images
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T16:46:24.56798+00:00
-- url     : https://prove2.me/submissions/43fb0025-6ca2-4fb6-ad5b-97244b5b482b

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
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_isProP_of_quotient_images

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

variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]

/-- Closed subgroups are separated by their images in finite continuous
quotients. This supplies the separation step of the compactness argument. -/
private theorem mem_of_mem_sup_openNormal (H : Subgroup G) (hH : IsClosed (H : Set G))
    (x : G) (hx : ∀ U : OpenNormalSubgroup G, x ∈ H ⊔ U.toSubgroup) : x ∈ H := by
  let HC : ClosedSubgroup G := { toSubgroup := H, isClosed' := hH }
  change x ∈ HC.toSubgroup
  rw [ProfiniteGrp.closedSubgroup_eq_sInf_open HC]
  apply Subgroup.mem_sInf.mpr
  intro V hV
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    hV.1 V.one_mem
  exact (sup_le hV.2 hU) (hx U)





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





private theorem isSylowPro_of_full_images_preparedProof {p : ℕ} (P : Subgroup G)
    (hP : IsClosed (P : Set G))
    (hfull : ∀ U : OpenNormalSubgroup G, ∃ S : Sylow p (G ⧸ U.toSubgroup),
      P.map (QuotientGroup.mk' U.toSubgroup) = (S : Subgroup _)) :
    IsSylowPro p ⊤ P := by
  refine ⟨le_top, hP, isProP_of_quotient_images P ?_, ?_⟩
  · intro U
    obtain ⟨S, hS⟩ := hfull U
    rw [hS]
    exact S.isPGroup'
  · intro Q _ _ hQ hPQ
    apply le_antisymm _ hPQ
    intro x hx
    apply mem_of_mem_sup_openNormal P hP x
    intro U
    let π := QuotientGroup.mk' U.toSubgroup
    obtain ⟨S, hS⟩ := hfull U
    have he : Q.map π = (S : Subgroup _) := S.is_maximal'
      (isPGroup_quotient_image Q hQ U) (hS.symm.le.trans (Subgroup.map_mono hPQ))
    have hm : π x ∈ P.map π := by
      rw [hS, ← he]
      exact Subgroup.mem_map_of_mem π hx
    change x ∈ (P.map π).comap π at hm
    simpa only [Subgroup.comap_map_eq, π, QuotientGroup.ker_mk'] using hm























end LocalConjugacy

end LocalConjugacy.Proof

end

universe u

theorem solution :
∀ {G : Type u} [inst : Group.{u} G] [inst_1 : TopologicalSpace.{u} G]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u} G inst inst_1] {p : Nat} (P : @Subgroup.{u} G inst)
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
  @LocalConjugacy.Proof.LocalConjugacy.IsSylowPro.{u} p G inst inst_1
    (@Top.top.{u} (@Subgroup.{u} G inst) (@Subgroup.instTop.{u} G inst)) P :=
  @LocalConjugacy.Proof.LocalConjugacy.isSylowPro_of_full_images_preparedProof
