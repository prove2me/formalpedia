-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.supplements_of_locallyContains
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T17:25:36.597531+00:00
-- url     : https://prove2.me/submissions/ebfcd5c6-efc3-48d4-b788-1aa5a6927320

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
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_finite_supplements_of_locallyContains
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

private theorem sup_eq_top_of_supplements (N H : Subgroup G) (h : Supplements N H) :
    N ⊔ H = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨n, hn, y, hy, rfl⟩ := h x
  exact (N ⊔ H).mul_mem ((show N ≤ N ⊔ H from le_sup_left) hn)
    ((show H ≤ N ⊔ H from le_sup_right) hy)

private theorem supplements_of_sup_eq_top (N H : Subgroup G) [N.Normal]
    (h : N ⊔ H = ⊤) : Supplements N H := by
  intro x
  have he := Subgroup.normal_mul N H
  rw [h] at he
  have hx : x ∈ (N : Set G) * (H : Set G) := by rw [← he]; trivial
  exact hx

private theorem supplements_map (N H : Subgroup G) (h : Supplements N H)
    (f : G →* F) (hf : Function.Surjective f) : Supplements (N.map f) (H.map f) := by
  intro y
  obtain ⟨x, rfl⟩ := hf y
  obtain ⟨n, hn, z, hz, rfl⟩ := h x
  exact ⟨f n, Subgroup.mem_map_of_mem f hn, f z, Subgroup.mem_map_of_mem f hz,
    (map_mul f n z).symm⟩







end Algebra

end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy
open scoped Pointwise





/-- The supplementary-subgroup assertion used implicitly in the paper's
proofs of Corollary 1.3 and the fixed-point results. -/
private theorem supplements_of_locallyContains_preparedProof {G : Type*} [Group G] [TopologicalSpace G]
    [Profinite G] (N H J : Subgroup G) [N.Normal]
    (hN : IsClosed (N : Set G)) (hH : IsClosed (H : Set G))
    (hJ : IsClosed (J : Set G)) (hNJ : Supplements N J)
    (hloc : LocallyContains H J) : Supplements N H := by
  have hc : IsClosed ((N ⊔ H : Subgroup G) : Set G) := by
    rw [Subgroup.normal_mul]
    exact (hN.isCompact.mul hH.isCompact).isClosed
  apply supplements_of_sup_eq_top N H
  apply top_unique
  intro x _
  apply mem_of_mem_sup_openNormal (N ⊔ H) hc x
  intro U
  let π := QuotientGroup.mk' U.toSubgroup
  have hf := finite_supplements_of_locallyContains (N.map π) (H.map π) (J.map π)
    (supplements_map N J hNJ π (QuotientGroup.mk'_surjective _))
    (locallyContains_map_finite H J hJ hloc π continuous_quotient_mk')
  have he : (N ⊔ H).map π = ⊤ := by
    rw [Subgroup.map_sup]
    exact sup_eq_top_of_supplements _ _ hf
  have hm : π x ∈ (N ⊔ H).map π := by rw [he]; trivial
  change x ∈ ((N ⊔ H).map π).comap π at hm
  simpa only [Subgroup.comap_map_eq, π, QuotientGroup.ker_mk'] using hm

end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1

theorem solution :
∀ {G : Type u_1} [inst : Group.{u_1} G] [inst_1 : TopologicalSpace.{u_1} G]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} G inst inst_1] (N H J : @Subgroup.{u_1} G inst)
  [@Subgroup.Normal.{u_1} G inst N]
  (hN :
    @IsClosed.{u_1} G inst_1
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst) N))
  (hH :
    @IsClosed.{u_1} G inst_1
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst) H))
  (hJ :
    @IsClosed.{u_1} G inst_1
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst) J))
  (hNJ : @LocalConjugacy.Proof.LocalConjugacy.Supplements.{u_1} G inst N J)
  (hloc : @LocalConjugacy.Proof.LocalConjugacy.LocallyContains.{u_1} G inst inst_1 H J),
  @LocalConjugacy.Proof.LocalConjugacy.Supplements.{u_1} G inst N H :=
  @LocalConjugacy.Proof.LocalConjugacy.supplements_of_locallyContains_preparedProof
