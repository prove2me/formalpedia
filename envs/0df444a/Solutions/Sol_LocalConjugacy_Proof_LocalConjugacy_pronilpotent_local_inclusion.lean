-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.pronilpotent_local_inclusion
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T18:15:31.52505+00:00
-- url     : https://prove2.me/submissions/fae740e4-426f-4f78-b879-f1bbd4e67c26

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
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_locallyConjugate_of_locallyContains_complement
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_profinite_quotient
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_sylowPro_map
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_theorem_1_1

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

section Algebra
variable {G F : Type*} [Group G] [Group F]





end Algebra

section Topology
variable {G F : Type*} [Group G] [Group F]
  [TopologicalSpace G] [TopologicalSpace F] [DiscreteTopology F]

/-- A continuous discrete quotient of a pronilpotent group is nilpotent. -/
private theorem nilpotent_of_pronilpotent_surjective (hG : Pronilpotent G)
    (f : G →* F) (hf : Continuous f) (hs : Function.Surjective f) : Group.IsNilpotent F := by
  let U : OpenNormalSubgroup G :=
    { toSubgroup := f.ker
      isOpen' := hf.isOpen_preimage _ (isOpen_discrete {1}) }
  letI := hG U
  exact Group.nilpotent_of_surjective (QuotientGroup.kerLift f)
    (QuotientGroup.lift_surjective_of_surjective _ f hs le_rfl)

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

/-! Algebraic quotient reduction from the earlier local development, rechecked here. -/

namespace LocalConjugacy

open Subgroup QuotientGroup

variable {G : Type*} [Group G]



/-- **Step 1.** If `H` supplements the normal subgroup `N` and `N ⊓ H` is normalised by `N`,
then `N ⊓ H` is normal in the whole group.  (`N ⊓ H` is always normalised by `H`; the new
hypothesis supplies the other half, and `N ⊔ H = ⊤` glues them.) -/
private theorem inf_normal_of_stabNormal (N H : Subgroup G) [hN : N.Normal]
    (hsup : N ⊔ H = ⊤) (hstab : StabNormal N H) : (N ⊓ H).Normal := by
  rw [← normalizer_eq_top_iff, eq_top_iff, ← hsup]
  refine sup_le (le_normalizer_iff.mpr hstab) (le_normalizer_iff.mpr ?_)
  intro h hh d hd
  exact ⟨hN.conj_mem d hd.1 h, H.mul_mem (H.mul_mem hh hd.2) (H.inv_mem hh)⟩

/-- **Step 2.** Once `D = N ⊓ H` is normal, the image of `H` in `G ⧸ D` is a genuine complement
to the image of `N` — so the conjugacy theorem for complements becomes applicable. -/
private theorem isComplement'_map_mk' (N H : Subgroup G) [N.Normal] [(N ⊓ H).Normal]
    (hsup : N ⊔ H = ⊤) :
    IsComplement' (N.map (mk' (N ⊓ H))) (H.map (mk' (N ⊓ H))) := by
  have hsurj : Function.Surjective (mk' (N ⊓ H)) := mk'_surjective _
  refine isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [disjoint_iff_inf_le]
    rintro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hx1
    obtain ⟨h, hh, hnh⟩ := Subgroup.mem_map.mp hx2
    obtain ⟨z, hz, hzz⟩ := (mk'_eq_mk' _).mp hnh.symm
    have hnH : n ∈ H := by
      have hz' : h * z⁻¹ ∈ H := H.mul_mem hh (H.inv_mem hz.2)
      rwa [← hzz, mul_inv_cancel_right] at hz'
    have : n ∈ N ⊓ H := ⟨hn, hnH⟩
    simpa using (QuotientGroup.eq_one_iff (N := N ⊓ H) n).mpr this
  · have hmap : (N.map (mk' (N ⊓ H))) ⊔ (H.map (mk' (N ⊓ H))) = ⊤ := by
      rw [← Subgroup.map_sup, hsup, Subgroup.map_top_of_surjective _ hsurj]
    have := Subgroup.normal_mul (N.map (mk' (N ⊓ H))) (H.map (mk' (N ⊓ H)))
    rw [hmap] at this
    simpa using this.symm





end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy
open scoped Pointwise

section Algebra
variable {G F : Type*} [Group G] [Group F]

private theorem sup_eq_top_of_supplements (N H : Subgroup G) (h : Supplements N H) :
    N ⊔ H = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨n, hn, y, hy, rfl⟩ := h x
  exact (N ⊔ H).mul_mem ((show N ≤ N ⊔ H from le_sup_left) hn)
    ((show H ≤ N ⊔ H from le_sup_right) hy)



private theorem supplements_map (N H : Subgroup G) (h : Supplements N H)
    (f : G →* F) (hf : Function.Surjective f) : Supplements (N.map f) (H.map f) := by
  intro y
  obtain ⟨x, rfl⟩ := hf y
  obtain ⟨n, hn, z, hz, rfl⟩ := h x
  exact ⟨f n, Subgroup.mem_map_of_mem f hn, f z, Subgroup.mem_map_of_mem f hz,
    (map_mul f n z).symm⟩





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

section Descent
variable {J F N : Type*} [Group J] [Group F] [Group N]
  [TopologicalSpace J] [TopologicalSpace F] [TopologicalSpace N]
  [MulDistribMulAction J N] [MulDistribMulAction F N]



private theorem subgroupImageHom_surjective (P : Subgroup J) (π : J →* F) :
    Function.Surjective (subgroupImageHom P π) := by
  rintro ⟨_, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

namespace Cocycle


variable (P : Subgroup J) (π : J →* F)
  (ha : ∀ (j : J) (n : N), π j • n = j • n) (f : Cocycle (N := N) P)
  (hf : ∀ x y : P, π x = π y → f.toFun x = f.toFun y)











end Cocycle
end Descent

section OpenNormal
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [DiscreteTopology N]
  [MulDistribMulAction J N] [ContinuousSMul J N] [Finite N]





end OpenNormal
end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

section Maps
variable {G F : Type*} [Group G] [Group F]
  [TopologicalSpace G] [TopologicalSpace F] [IsTopologicalGroup F]

private theorem pronilpotent_of_continuous_surjective (hG : Pronilpotent G)
    (f : G →* F) (hf : Continuous f) (hs : Function.Surjective f) : Pronilpotent F := by
  intro U
  exact nilpotent_of_pronilpotent_surjective hG
    ((QuotientGroup.mk' U.toSubgroup).comp f)
    (continuous_quotient_mk'.comp hf) ((QuotientGroup.mk'_surjective U.toSubgroup).comp hs)

private theorem prosupersolvable_of_continuous_surjective (hG : Prosupersolvable G)
    (f : G →* F) (hf : Continuous f) (hs : Function.Surjective f) : Prosupersolvable F := by
  intro U
  exact supersolvable_of_prosupersolvable_surjective hG
    ((QuotientGroup.mk' U.toSubgroup).comp f)
    (continuous_quotient_mk'.comp hf) ((QuotientGroup.mk'_surjective U.toSubgroup).comp hs)

end Maps

section Algebra
variable {G : Type*} [Group G]









end Algebra

section Topology
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]







end Topology
end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy
open Topology



section Images
variable {G F : Type*} [Group G] [Group F] [TopologicalSpace G] [TopologicalSpace F]
  [Profinite G] [Profinite F]





private theorem locallyContains_map (H K : Subgroup G) (hK : IsClosed (K : Set G))
    (hlocal : LocallyContains H K) (f : G →* F) (hf : Continuous f) :
    LocallyContains (H.map f) (K.map f) := by
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP, g, hg⟩ := hlocal p hp
  refine ⟨P.map f, sylowPro_map K P hK hP f hf, f g, ?_⟩
  rw [← conjugate_map]
  exact Subgroup.map_mono hg



end Images
end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

section Maps
variable {G F : Type*} [Group G] [Group F] [TopologicalSpace G] [TopologicalSpace F]
  [IsTopologicalGroup G] [IsTopologicalGroup F]

private theorem pronilpotent_subgroup_image (N : Subgroup G) (hN : Pronilpotent N)
    (f : G →* F) (hf : Continuous f) : Pronilpotent (N.map f) :=
  pronilpotent_of_continuous_surjective hN (subgroupImageHom N f)
    ((hf.comp continuous_subtype_val).subtype_mk _) (subgroupImageHom_surjective N f)







private theorem pronilpotent_quotient_image (N : Subgroup G) [N.Normal]
    (f : G →* F) (hf : Continuous f) (hs : Function.Surjective f) [(N.map f).Normal]
    (h : Pronilpotent (G ⧸ N)) : Pronilpotent (F ⧸ N.map f) := by
  let φ := QuotientGroup.map N (N.map f) f (Subgroup.le_comap_map f N)
  apply pronilpotent_of_continuous_surjective h φ
  · apply (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr
    exact continuous_quotient_mk'.comp hf
  · intro y
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (N.map f) y
    obtain ⟨x, rfl⟩ := hs z
    exact ⟨QuotientGroup.mk' N x, rfl⟩

end Maps

end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy


section Profinite
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]



/-- The normal-intersection quotient reduction, using images throughout.
This permits arbitrary closed supplements before passing to the quotient. -/
private theorem pronilpotent_local_inclusion_preparedProof (N H K : Subgroup G) [N.Normal]
    (hN : IsClosed (N : Set G)) (hH : IsClosed (H : Set G)) (hK : IsClosed (K : Set G))
    (hpron : Pronilpotent N) (hcase : Prosupersolvable G ∨ Pronilpotent (G ⧸ N))
    (hsH : Supplements N H) (hsK : Supplements N K)
    (hnormal : IntersectionNormal N H) (hloc : LocallyContains H K) :
    ∃ g : G, conjugate g K ≤ H := by
  letI := inf_normal_of_stabNormal N H (sup_eq_top_of_supplements N H hsH) hnormal
  let D := N ⊓ H
  have hD : IsClosed (D : Set G) := hN.inter hH
  letI := profinite_quotient D hD
  let π := QuotientGroup.mk' D
  have hNq : IsClosed (N.map π : Set (G ⧸ D)) := (hN.isCompact.image continuous_quotient_mk').isClosed
  have hHq : IsClosed (H.map π : Set (G ⧸ D)) := (hH.isCompact.image continuous_quotient_mk').isClosed
  have hKq : IsClosed (K.map π : Set (G ⧸ D)) := (hK.isCompact.image continuous_quotient_mk').isClosed
  have hsHq := supplements_map N H hsH π (QuotientGroup.mk'_surjective D)
  have hsKq := supplements_map N K hsK π (QuotientGroup.mk'_surjective D)
  have hc := isComplement'_map_mk' N H (sup_eq_top_of_supplements N H hsH)
  have hl := locallyContains_map H K hK hloc π continuous_quotient_mk'
  have hcaseq : Prosupersolvable (G ⧸ D) ∨ Pronilpotent ((G ⧸ D) ⧸ N.map π) := by
    rcases hcase with h | h
    · exact Or.inl (prosupersolvable_of_continuous_surjective h π continuous_quotient_mk'
        (QuotientGroup.mk'_surjective D))
    · exact Or.inr (pronilpotent_quotient_image N π continuous_quotient_mk'
        (QuotientGroup.mk'_surjective D) h)
  have hconj := (theorem_1_1 (N.map π) (K.map π) (H.map π) hNq hKq hHq
    (pronilpotent_subgroup_image N hpron π continuous_quotient_mk') hcaseq hsKq hsHq).mpr
      (locallyConjugate_of_locallyContains_complement _ _ _ hNq hHq hKq hc hsKq hl)
  obtain ⟨q, hq⟩ := hconj
  exact conjugate_le_of_quotient D H K inf_le_right q hq.le



end Profinite
end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1

theorem solution :
∀ {G : Type u_1} [inst : Group.{u_1} G] [inst_1 : TopologicalSpace.{u_1} G]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} G inst inst_1] (N H K : @Subgroup.{u_1} G inst)
  [inst_3 : @Subgroup.Normal.{u_1} G inst N]
  (hN :
    @IsClosed.{u_1} G inst_1
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst) N))
  (hH :
    @IsClosed.{u_1} G inst_1
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst) H))
  (hK :
    @IsClosed.{u_1} G inst_1
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst) K))
  (hpron :
    @LocalConjugacy.Proof.LocalConjugacy.Pronilpotent.{u_1}
      (@Subtype.{u_1 + 1} G fun (x : G) =>
        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)
      (@Subgroup.toGroup.{u_1} G inst N)
      (@instTopologicalSpaceSubtype.{u_1} G
        (fun (x : G) =>
          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)
        inst_1))
  (hcase :
    Or (@LocalConjugacy.Proof.LocalConjugacy.Prosupersolvable.{u_1} G inst inst_1)
      (@LocalConjugacy.Proof.LocalConjugacy.Pronilpotent.{u_1}
        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst) N)
        (@QuotientGroup.Quotient.group.{u_1} G inst N inst_3)
        (@QuotientGroup.instTopologicalSpace.{u_1} G inst_1 inst N)))
  (hsH : @LocalConjugacy.Proof.LocalConjugacy.Supplements.{u_1} G inst N H)
  (hsK : @LocalConjugacy.Proof.LocalConjugacy.Supplements.{u_1} G inst N K)
  (hnormal : @LocalConjugacy.Proof.LocalConjugacy.IntersectionNormal.{u_1} G inst N H)
  (hloc : @LocalConjugacy.Proof.LocalConjugacy.LocallyContains.{u_1} G inst inst_1 H K),
  @Exists.{u_1 + 1} G fun (g : G) =>
    @LE.le.{u_1} (@Subgroup.{u_1} G inst)
      (@Preorder.toLE.{u_1} (@Subgroup.{u_1} G inst)
        (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instPartialOrder.{u_1} G inst)))
      (@LocalConjugacy.Proof.LocalConjugacy.conjugate.{u_1} G inst g K) H :=
  @LocalConjugacy.Proof.LocalConjugacy.pronilpotent_local_inclusion_preparedProof
