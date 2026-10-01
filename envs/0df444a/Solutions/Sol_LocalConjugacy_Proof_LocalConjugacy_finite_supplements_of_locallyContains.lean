-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.finite_supplements_of_locallyContains
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T17:13:27.879704+00:00
-- url     : https://prove2.me/submissions/9ef04471-3be7-4725-a06c-3f980cc7c140

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
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_sylowPro_map_finite

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

variable {G F : Type*} [Group G] [Group F]









private theorem conjugate_map (f : G →* F) (g : G) (H : Subgroup G) :
    (conjugate g H).map f = conjugate (f g) (H.map f) := by
  unfold conjugate
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]



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



private theorem supplements_of_sup_eq_top (N H : Subgroup G) [N.Normal]
    (h : N ⊔ H = ⊤) : Supplements N H := by
  intro x
  have he := Subgroup.normal_mul N H
  rw [h] at he
  have hx : x ∈ (N : Set G) * (H : Set G) := by rw [← he]; trivial
  exact hx









end Algebra

end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy
open scoped Pointwise

private theorem finite_eq_top_of_locallyContains {G : Type*} [Group G] [Finite G]
    [TopologicalSpace G] [DiscreteTopology G] (H : Subgroup G)
    (hloc : LocallyContains H ⊤) : H = ⊤ := by
  apply H.index_eq_one.mp
  apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
  intro p hp hd
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP, g, hg⟩ := hloc p hp
  obtain ⟨S, hS⟩ := sylow_of_isSylowPro P hP
  have he : (g • S).toSubgroup ≤ H := by
    rw [sylow_smul_toSubgroup, hS]
    exact hg
  exact (g • S).not_dvd_index (hd.trans (Subgroup.index_dvd_of_le he))

private theorem finite_supplements_of_locallyContains_preparedProof {G : Type*} [Group G] [Finite G]
    [TopologicalSpace G] [DiscreteTopology G] (N H J : Subgroup G) [N.Normal]
    (hNJ : Supplements N J) (hloc : LocallyContains H J) : Supplements N H := by
  letI : Profinite G := ⟨⟩
  let π := QuotientGroup.mk' N
  have hj : J.map π = ⊤ := by
    apply top_unique
    intro q _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
    obtain ⟨n, hn, j, hj, rfl⟩ := hNJ x
    refine ⟨j, hj, ?_⟩
    have hn' : π n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    change π j = π (n * j)
    simp only [map_mul, hn', one_mul]
  have hl : LocallyContains (H.map π) ⊤ := by
    rw [← hj]
    exact locallyContains_map_finite H J (isClosed_discrete _) hloc π continuous_quotient_mk'
  have he := congrArg (fun L : Subgroup (G ⧸ N) => L.comap π)
    (finite_eq_top_of_locallyContains (H.map π) hl)
  apply supplements_of_sup_eq_top N H
  simpa only [Subgroup.comap_map_eq, π, QuotientGroup.ker_mk', Subgroup.comap_top,
    sup_comm H N] using he



end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1

theorem solution :
∀ {G : Type u_1} [inst : Group.{u_1} G] [Finite.{u_1 + 1} G] [inst_2 : TopologicalSpace.{u_1} G]
  [@DiscreteTopology.{u_1} G inst_2] (N H J : @Subgroup.{u_1} G inst) [@Subgroup.Normal.{u_1} G inst N]
  (hNJ : @LocalConjugacy.Proof.LocalConjugacy.Supplements.{u_1} G inst N J)
  (hloc : @LocalConjugacy.Proof.LocalConjugacy.LocallyContains.{u_1} G inst inst_2 H J),
  @LocalConjugacy.Proof.LocalConjugacy.Supplements.{u_1} G inst N H :=
  @LocalConjugacy.Proof.LocalConjugacy.finite_supplements_of_locallyContains_preparedProof
