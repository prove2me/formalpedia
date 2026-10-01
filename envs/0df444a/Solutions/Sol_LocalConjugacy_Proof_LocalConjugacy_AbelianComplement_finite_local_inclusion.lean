-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.AbelianComplement.finite_local_inclusion
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T16:43:59.336979+00:00
-- url     : https://prove2.me/submissions/73bda054-247d-4c5b-b1b1-a8f62193d444

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
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_AbelianComplement_conjugate_le_of_coboundary
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_AbelianComplement_projection_mul
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_FiniteAbelianCohomology_local_coboundary
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_isSylowPro_subgroupOf

/-! Kernel-checked proof and its local helpers, retaining their original scopes. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

private theorem proP_of_isPGroup {G : Type*} [Group G] [TopologicalSpace G]
    {p : ℕ} (h : IsPGroup p G) : IsProP p G :=
  fun U => h.to_quotient U.toSubgroup

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

/-- In a discrete group, the profinite condition reduces to the ordinary
torsion definition of a `p`-group. -/
private theorem isProP_iff_isPGroup {G : Type*} [Group G] [TopologicalSpace G]
    [DiscreteTopology G] (p : ℕ) : IsProP p G ↔ IsPGroup p G :=
  ⟨fun h x => image_pow h (MonoidHom.id G) continuous_id x,
   proP_of_isPGroup⟩





private theorem sylow_of_isSylowPro {G : Type*} [Group G] [TopologicalSpace G]
    [DiscreteTopology G] {p : ℕ} (P : Subgroup G) (hP : IsSylowPro p ⊤ P) :
    ∃ S : Sylow p G, S.toSubgroup = P := by
  exact ⟨⟨P, (isProP_iff_isPGroup p).mp hP.2.2.1,
    fun hQ hPQ => hP.2.2.2 _ le_top (isClosed_discrete _) (proP_of_isPGroup hQ) hPQ⟩, rfl⟩

end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy
namespace AbelianComplement

variable {G : Type*} [Group G] (N H : Subgroup G) [N.Normal]
  (hc : Subgroup.IsComplement' N H)



private theorem projection_mul_right (x : G) {h : G} (hh : h ∈ H) :
    projection N H hc (x * h) = projection N H hc x := by
  have he := congrArg Prod.fst (hc.equiv_mul_right_of_mem (g := x) hh)
  exact he







private theorem local_fixed_cocycle (hcomm : ∀ n m : N, n * m = m * n)
    (P : Subgroup G) (g : G) (hg : conjugate g P ≤ H) :
    ∃ n : N, ∀ x : P, projection N H hc x * MulAut.conjNormal (x : G) n = n := by
  refine ⟨projection N H hc g⁻¹, fun x => ?_⟩
  rw [← projection_mul N H hc hcomm]
  have hm : g * x * g⁻¹ ∈ H := hg (Subgroup.mem_map_of_mem _ x.property)
  have he : (x : G) * g⁻¹ = g⁻¹ * (g * x * g⁻¹) := by group
  rw [he]
  exact projection_mul_right N H hc g⁻¹ hm



include hc in
private theorem finite_local_inclusion_preparedProof [Finite G] [TopologicalSpace G] [DiscreteTopology G]
    (hcomm : ∀ n m : N, n * m = m * n) (K : Subgroup G)
    (hloc : LocallyContains H K) : ∃ g : G, conjugate g K ≤ H := by
  classical
  letI : Profinite G := ⟨⟩
  letI : CommGroup N := { (inferInstance : Group N) with mul_comm := hcomm }
  letI : Fintype K := Fintype.ofFinite K
  let a : K →* MulAut N := MulAut.conjNormal.comp K.subtype
  let f : K → N := fun x => projection N H hc x
  have hf : CocycleFn a f := fun x y => projection_mul N H hc hcomm x y
  have hl : ∀ p : ℕ, p.Prime → ∃ P : Sylow p K, ∃ n : N,
      ∀ x : P, f x * a x n = n := by
    intro p hp
    obtain ⟨P, hP, g, hg⟩ := hloc p hp
    obtain ⟨S, hS⟩ := sylow_of_isSylowPro (P.subgroupOf K)
      (isSylowPro_subgroupOf K P (isClosed_discrete _) hP)
    obtain ⟨n, hn⟩ := local_fixed_cocycle N H hc hcomm P g hg
    refine ⟨S, n, fun x => ?_⟩
    have hx : ((x : K) : G) ∈ P := by
      have hx := x.property
      change (x : K) ∈ S.toSubgroup at hx
      rw [hS] at hx
      exact hx
    exact hn ⟨x, hx⟩
  obtain ⟨b, hb⟩ := FiniteAbelianCohomology.local_coboundary a f hf hl
  exact ⟨b, conjugate_le_of_coboundary N H hc hcomm K b hb⟩

end AbelianComplement
end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1

theorem solution :
∀ {G : Type u_1} [inst : Group.{u_1} G] (N H : @Subgroup.{u_1} G inst) [@Subgroup.Normal.{u_1} G inst N]
  (hc : @Subgroup.IsComplement'.{u_1} G inst N H) [Finite.{u_1 + 1} G] [inst_3 : TopologicalSpace.{u_1} G]
  [@DiscreteTopology.{u_1} G inst_3]
  (hcomm :
    ∀
      (n m :
        @Subtype.{u_1 + 1} G fun (x : G) =>
          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x),
      @Eq.{u_1 + 1}
        (@Subtype.{u_1 + 1} G fun (x : G) =>
          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)
        (@HMul.hMul.{u_1, u_1, u_1}
          (@Subtype.{u_1 + 1} G fun (x : G) =>
            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)
          (@Subtype.{u_1 + 1} G fun (x : G) =>
            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)
          (@Subtype.{u_1 + 1} G fun (x : G) =>
            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)
          (@instHMul.{u_1}
            (@Subtype.{u_1 + 1} G fun (x : G) =>
              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N
                x)
            (@Subgroup.mul.{u_1} G inst N))
          n m)
        (@HMul.hMul.{u_1, u_1, u_1}
          (@Subtype.{u_1 + 1} G fun (x : G) =>
            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)
          (@Subtype.{u_1 + 1} G fun (x : G) =>
            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)
          (@Subtype.{u_1 + 1} G fun (x : G) =>
            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)
          (@instHMul.{u_1}
            (@Subtype.{u_1 + 1} G fun (x : G) =>
              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N
                x)
            (@Subgroup.mul.{u_1} G inst N))
          m n))
  (K : @Subgroup.{u_1} G inst) (hloc : @LocalConjugacy.Proof.LocalConjugacy.LocallyContains.{u_1} G inst inst_3 H K),
  @Exists.{u_1 + 1} G fun (g : G) =>
    @LE.le.{u_1} (@Subgroup.{u_1} G inst)
      (@Preorder.toLE.{u_1} (@Subgroup.{u_1} G inst)
        (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instPartialOrder.{u_1} G inst)))
      (@LocalConjugacy.Proof.LocalConjugacy.conjugate.{u_1} G inst g K) H :=
  @LocalConjugacy.Proof.LocalConjugacy.AbelianComplement.finite_local_inclusion_preparedProof
