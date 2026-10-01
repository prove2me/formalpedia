-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.abelian_complement_inclusion_finite_kernel
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T16:51:28.971336+00:00
-- url     : https://prove2.me/submissions/ce1bb0c4-c597-47b8-b331-f64b62b605e2

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
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_AbelianComplement_finite_local_inclusion
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_sylowPro_map_finite

/-! Kernel-checked proof and its local helpers, retaining their original scopes. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

variable {G F : Type*} [Group G] [Group F]









private theorem conjugate_map (f : G →* F) (g : G) (H : Subgroup G) :
    (conjugate g H).map f = conjugate (f g) (H.map f) := by
  unfold conjugate
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]





end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

variable {G F : Type*} [Group G] [Group F] [TopologicalSpace G]
  [TopologicalSpace F] [Profinite G] [Finite F] [DiscreteTopology F]





private theorem locallyContains_map_finite (H K : Subgroup G)
    (hK : IsClosed (K : Set G)) (hlocal : LocallyContains H K)
    (f : G →* F) (hf : Continuous f) : LocallyContains (H.map f) (K.map f) := by
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP, g, hg⟩ := hlocal p hp
  refine ⟨P.map f, sylowPro_map_finite K P hK hP f hf, f g, ?_⟩
  rw [← conjugate_map]
  exact Subgroup.map_mono hg

end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy
open scoped Pointwise

section Algebra
variable {G F : Type*} [Group G] [Group F]





private theorem supplements_map (N H : Subgroup G) (h : Supplements N H)
    (f : G →* F) (hf : Function.Surjective f) : Supplements (N.map f) (H.map f) := by
  intro y
  obtain ⟨x, rfl⟩ := hf y
  obtain ⟨n, hn, z, hz, rfl⟩ := h x
  exact ⟨f n, Subgroup.mem_map_of_mem f hn, f z, Subgroup.mem_map_of_mem f hz,
    (map_mul f n z).symm⟩

private theorem commutative_map (N : Subgroup G) (hcomm : ∀ n m : N, n * m = m * n)
    (f : G →* F) : ∀ n m : N.map f, n * m = m * n := by
  rintro ⟨_, x, hx, rfl⟩ ⟨_, y, hy, rfl⟩
  apply Subtype.ext
  change f x * f y = f y * f x
  rw [← map_mul, ← map_mul]
  exact congrArg f (congrArg Subtype.val (hcomm ⟨x, hx⟩ ⟨y, hy⟩))



private theorem conjugate_le_of_quotient (D H K : Subgroup G) [D.Normal] (hDH : D ≤ H)
    (q : G ⧸ D) (hq : conjugate q (K.map (QuotientGroup.mk' D)) ≤
      H.map (QuotientGroup.mk' D)) : ∃ g : G, conjugate g K ≤ H := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective D q
  refine ⟨g, ?_⟩
  intro x hx
  let π := QuotientGroup.mk' D
  have hm : π x ∈ H.map π := by
    apply hq
    rw [← conjugate_map]
    exact Subgroup.mem_map_of_mem π hx
  change x ∈ (H.map π).comap π at hm
  simpa only [Subgroup.comap_map_eq, π, QuotientGroup.ker_mk', sup_eq_left.mpr hDH] using hm

end Algebra

end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

section Maps
variable {G F : Type*} [Group G] [Group F]
  [TopologicalSpace G] [TopologicalSpace F] [IsTopologicalGroup F]





end Maps

section Algebra
variable {G : Type*} [Group G]

private theorem isComplement'_of_supplements_inf (N H : Subgroup G)
    (hs : Supplements N H) (hd : N ⊓ H = ⊥) : Subgroup.IsComplement' N H := by
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hd)
  apply Set.eq_univ_of_forall
  intro g
  exact hs g







end Algebra

section Topology
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]







end Topology
end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

/-! The reductions needed to run Proposition 3.2's induction on `|N|`
while the ambient profinite group is allowed to be infinite. -/

namespace LocalConjugacy

section Algebra
variable {G : Type*} [Group G]

private theorem finiteIndex_of_finite_supplement (N H : Subgroup G) [Finite N]
    (hs : Supplements N H) : H.FiniteIndex := by
  let f : N → G ⧸ H := fun n => QuotientGroup.mk (n : G)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨n, hn, h, hh, rfl⟩ := hs x
    refine ⟨⟨n, hn⟩, QuotientGroup.eq.mpr ?_⟩
    simpa only [inv_mul_cancel_left] using hh
  letI : Finite (G ⧸ H) := Finite.of_surjective f hf
  exact Subgroup.finiteIndex_of_finite_quotient







end Algebra

section Topology
variable {G F : Type*} [Group G] [Group F]
  [TopologicalSpace G] [Profinite G] [TopologicalSpace F] [Profinite F]







end Topology

section Profinite
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]









end Profinite
end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

/-! The finite-normal-subgroup stage of Proposition 4.1. The ambient group
remains profinite. The complement case is reduced to a finite quotient in
which the complement survives, so the proved abelian cocycle argument supplies
the role of the conjugacy theorem cited in the manuscript. -/

namespace LocalConjugacy

private theorem abelian_complement_inclusion_finite_kernel_preparedProof
    {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]
    (N H K : Subgroup G) [N.Normal] [Finite N]
    (hH : IsClosed (H : Set G)) (hK : IsClosed (K : Set G))
    (hcomm : ∀ n m : N, n * m = m * n)
    (hs : Supplements N H) (hd : N ⊓ H = ⊥)
    (hlocal : LocallyContains H K) : ∃ g : G, conjugate g K ≤ H := by
  letI := finiteIndex_of_finite_supplement N H hs
  obtain ⟨U, hUH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (H.isOpen_of_isClosed_of_finiteIndex hH) H.one_mem
  let π := QuotientGroup.mk' U.toSubgroup
  have hdis : N.map π ⊓ H.map π = ⊥ := by
    apply eq_bot_iff.mpr
    rintro _ ⟨⟨n, hn, rfl⟩, hh⟩
    obtain ⟨h, hh, he⟩ := hh
    have hu : n⁻¹ * h ∈ U := QuotientGroup.eq.mp he.symm
    have hnH : n ∈ H := by
      have hm := H.mul_mem hh (H.inv_mem (hUH hu))
      simpa only [mul_inv_rev, inv_inv, mul_inv_cancel_left] using hm
    have hn1 : n = 1 := by
      have hm : n ∈ N ⊓ H := ⟨hn, hnH⟩
      simpa only [hd, Subgroup.mem_bot] using hm
    simpa only [hn1, map_one] using (Subgroup.one_mem (⊥ : Subgroup (G ⧸ U.toSubgroup)))
  have hc := isComplement'_of_supplements_inf (N.map π) (H.map π)
    (supplements_map N H hs π (QuotientGroup.mk'_surjective _)) hdis
  obtain ⟨q, hq⟩ := AbelianComplement.finite_local_inclusion (N.map π) (H.map π) hc
    (commutative_map N hcomm π) (K.map π)
    (locallyContains_map_finite H K hK hlocal π continuous_quotient_mk')
  exact conjugate_le_of_quotient U.toSubgroup H K hUH q hq



universe u





end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1

theorem solution :
∀ {G : Type u_1} [inst : Group.{u_1} G] [inst_1 : TopologicalSpace.{u_1} G]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} G inst inst_1] (N H K : @Subgroup.{u_1} G inst)
  [@Subgroup.Normal.{u_1} G inst N]
  [Finite.{u_1 + 1}
      (@Subtype.{u_1 + 1} G fun (x : G) =>
        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)]
  (hH :
    @IsClosed.{u_1} G inst_1
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst) H))
  (hK :
    @IsClosed.{u_1} G inst_1
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst) K))
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
  (hs : @LocalConjugacy.Proof.LocalConjugacy.Supplements.{u_1} G inst N H)
  (hd :
    @Eq.{u_1 + 1} (@Subgroup.{u_1} G inst)
      (@Min.min.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instMin.{u_1} G inst) N H)
      (@Bot.bot.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instBot.{u_1} G inst)))
  (hlocal : @LocalConjugacy.Proof.LocalConjugacy.LocallyContains.{u_1} G inst inst_1 H K),
  @Exists.{u_1 + 1} G fun (g : G) =>
    @LE.le.{u_1} (@Subgroup.{u_1} G inst)
      (@Preorder.toLE.{u_1} (@Subgroup.{u_1} G inst)
        (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instPartialOrder.{u_1} G inst)))
      (@LocalConjugacy.Proof.LocalConjugacy.conjugate.{u_1} G inst g K) H :=
  @LocalConjugacy.Proof.LocalConjugacy.abelian_complement_inclusion_finite_kernel_preparedProof
