-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.exists_procyclic_supplement
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T16:57:36.128209+00:00
-- url     : https://prove2.me/submissions/7b6dea79-6e55-4228-af7e-cf8d0739e95f

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
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_FiniteSylowSystem_map_subgroup
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_conjugate_le_full_sylow
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_isProP_of_quotient_images
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_isSylowPro_of_full_images
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_procyclic_zpowers_closure

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



private theorem isPGroup_map_of_continuous {G F : Type*} [Group G] [Group F]
    [TopologicalSpace G] [TopologicalSpace F] [DiscreteTopology F]
    {p : ℕ} (H : Subgroup G) (hH : IsProP p H) (f : G →* F) (hf : Continuous f) :
    IsPGroup p (H.map f) := by
  intro z
  obtain ⟨x, hx, he⟩ := z.property
  obtain ⟨k, hk⟩ := image_pow hH (f.comp H.subtype)
    (hf.comp continuous_subtype_val) ⟨x, hx⟩
  refine ⟨k, Subtype.ext ?_⟩
  change z.val ^ p ^ k = 1
  change f x ^ p ^ k = 1 at hk
  rwa [he] at hk





end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

variable {G F : Type*} [Group G] [Group F]

private theorem conjugate_comp (g h : G) (H : Subgroup G) :
    conjugate g (conjugate h H) = conjugate (g * h) H := by
  unfold conjugate
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

@[simp] private theorem conjugate_one (H : Subgroup G) : conjugate 1 H = H := by
  unfold conjugate
  have he : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  change H.map (MulAut.conj (1 : G)).toMonoidHom = H
  rw [he, Subgroup.map_id]

@[simp] private theorem conjugate_inv_cancel (g : G) (H : Subgroup G) :
    conjugate g⁻¹ (conjugate g H) = H := by
  rw [conjugate_comp, inv_mul_cancel, conjugate_one]

private theorem conjugate_mono (g : G) {H K : Subgroup G} (h : H ≤ K) :
    conjugate g H ≤ conjugate g K := Subgroup.map_mono h

private theorem conjugate_map (f : G →* F) (g : G) (H : Subgroup G) :
    (conjugate g H).map f = conjugate (f g) (H.map f) := by
  unfold conjugate
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

private theorem conjugate_le_iff (g : G) (H K : Subgroup G) :
    conjugate g H ≤ K ↔ H ≤ conjugate g⁻¹ K := by
  constructor
  · intro h
    simpa using conjugate_mono g⁻¹ h
  · intro h
    simpa only [conjugate_comp, mul_inv_cancel, conjugate_one] using conjugate_mono g h

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

private theorem isProP_mono {p : ℕ} {P H : Subgroup G} (hPH : P ≤ H)
    (hH : IsProP p H) : IsProP p P := by
  apply isProP_of_quotient_images
  intro U
  exact (isPGroup_quotient_image H hH U).to_le (Subgroup.map_mono hPH)

namespace FiniteSylowSystem
open CategoryTheory













private theorem exists_compatible (p : ℕ) [Fact p.Prime] :
    ∃ P : (U : OpenNormalSubgroup G) → Sylow p (G ⧸ U.toSubgroup),
      ∀ (U V : OpenNormalSubgroup G) (h : U ≤ V),
        (P U).mapSurjective (transition_surjective h) = P V := by
  let : ∀ U, Finite ((functor (G := G) p).obj U) := fun U =>
    inferInstanceAs (Finite (Sylow p (G ⧸ U.toSubgroup)))
  let : ∀ U, Nonempty ((functor (G := G) p).obj U) := fun U =>
    inferInstanceAs (Nonempty (Sylow p (G ⧸ U.toSubgroup)))
  obtain ⟨P, hP⟩ := nonempty_sections_of_finite_cofiltered_system (functor (G := G) p)
  exact ⟨P, fun U V h => hP (homOfLE h)⟩

variable {p : ℕ} [Fact p.Prime]
variable (P : (U : OpenNormalSubgroup G) → Sylow p (G ⧸ U.toSubgroup))
variable (hP : ∀ (U V : OpenNormalSubgroup G) (h : U ≤ V),
  (P U).mapSurjective (transition_surjective h) = P V)



private theorem mem_subgroup (x : G) :
    x ∈ subgroup P ↔ ∀ U, QuotientGroup.mk' U.toSubgroup x ∈ P U := by
  simp only [subgroup, Subgroup.mem_iInf, Subgroup.mem_comap]
  rfl

private theorem subgroup_closed : IsClosed (subgroup P : Set G) := by
  rw [show (subgroup P : Set G) = ⋂ U : OpenNormalSubgroup G,
    (QuotientGroup.mk' U.toSubgroup) ⁻¹' (P U).toSubgroup.carrier by
      ext x
      simp only [Set.mem_iInter, Set.mem_preimage]
      exact mem_subgroup P x]
  apply isClosed_iInter
  intro U
  have hc : IsClosed (P U).toSubgroup.carrier := isClosed_discrete _
  exact hc.preimage (continuous_quotient_mk' : Continuous (QuotientGroup.mk' U.toSubgroup))

include hP







end FiniteSylowSystem

/-- A profinite group has a closed pro-`p` subgroup whose image in every
continuous finite quotient is a Sylow subgroup. -/
private theorem exists_full_sylow (p : ℕ) [Fact p.Prime] :
    ∃ P : Subgroup G, IsClosed (P : Set G) ∧ IsProP p P ∧
      ∀ U : OpenNormalSubgroup G, ∃ S : Sylow p (G ⧸ U.toSubgroup),
        P.map (QuotientGroup.mk' U.toSubgroup) = (S : Subgroup _) := by
  obtain ⟨S, hS⟩ := FiniteSylowSystem.exists_compatible (G := G) p
  refine ⟨FiniteSylowSystem.subgroup S, FiniteSylowSystem.subgroup_closed S, ?_, ?_⟩
  · apply isProP_of_quotient_images
    intro U
    rw [FiniteSylowSystem.map_subgroup S hS U]
    exact (S U).isPGroup'
  · intro U
    exact ⟨S U, FiniteSylowSystem.map_subgroup S hS U⟩





private theorem exists_sylowPro (p : ℕ) [Fact p.Prime] :
    ∃ P : Subgroup G, IsSylowPro p ⊤ P := by
  obtain ⟨P, hc, _, hf⟩ := exists_full_sylow (G := G) p
  exact ⟨P, isSylowPro_of_full_images P hc hf⟩

private theorem conjugate_closed (g : G) (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    IsClosed (conjugate g H : Set G) := by
  have hc : Continuous (fun x : G => g * x * g⁻¹) :=
    (continuous_const.mul continuous_id).mul continuous_const
  exact (hH.isCompact.image hc).isClosed

private theorem conjugate_isProP {p : ℕ} (g : G) (H : Subgroup G) (hH : IsProP p H) :
    IsProP p (conjugate g H) := by
  apply isProP_of_quotient_images
  intro U
  unfold conjugate
  rw [Subgroup.map_map]
  apply isPGroup_map_of_continuous H hH
  exact continuous_quotient_mk'.comp
    ((continuous_const.mul continuous_id).mul continuous_const)

private theorem sylowPro_full_images {p : ℕ} [Fact p.Prime] (P : Subgroup G)
    (hP : IsSylowPro p ⊤ P) (U : OpenNormalSubgroup G) :
    ∃ S : Sylow p (G ⧸ U.toSubgroup),
      P.map (QuotientGroup.mk' U.toSubgroup) = (S : Subgroup _) := by
  obtain ⟨Q, hc, hp, hf⟩ := exists_full_sylow (G := G) p
  obtain ⟨g, hg⟩ := conjugate_le_full_sylow P Q hP.2.2.1 hc hf
  have he : conjugate g⁻¹ Q = P := hP.2.2.2 _ le_top
    (conjugate_closed g⁻¹ Q hc) (conjugate_isProP g⁻¹ Q hp)
    ((conjugate_le_iff g P Q).mp hg)
  obtain ⟨S, hS⟩ := hf U
  let π := QuotientGroup.mk' U.toSubgroup
  refine ⟨(π g⁻¹) • S, ?_⟩
  rw [← he, conjugate_map, hS]
  exact (sylow_smul_toSubgroup p (π g⁻¹) S).symm















end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

variable {G F : Type*} [Group G] [Group F] [TopologicalSpace G]
  [TopologicalSpace F] [Profinite G] [Finite F] [DiscreteTopology F]

private theorem sylowPro_map_surjective_finite {p : ℕ} [Fact p.Prime]
    (P : Subgroup G) (hP : IsSylowPro p ⊤ P) (f : G →* F)
    (hf : Continuous f) (hs : Function.Surjective f) :
    ∃ S : Sylow p F, P.map f = S.toSubgroup := by
  let U : OpenNormalSubgroup G :=
    { toSubgroup := f.ker
      isOpen' := hf.isOpen_preimage _ (isOpen_discrete {1}) }
  obtain ⟨S, hS⟩ := sylowPro_full_images P hP U
  let φ : G ⧸ U.toSubgroup →* F := QuotientGroup.kerLift f
  have hφ : Function.Surjective φ := QuotientGroup.lift_surjective_of_surjective _ f hs le_rfl
  refine ⟨S.mapSurjective hφ, ?_⟩
  change P.map f = (S.toSubgroup).map φ
  rw [← hS, Subgroup.map_map]
  rfl





end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]



/-- A closed normal subgroup of prime index has a closed procyclic pro-prime
supplement. The ambient profinite group need not be finite or solvable. -/
private theorem exists_procyclic_supplement_preparedProof (K : Subgroup G) [K.Normal]
    (hK : IsClosed (K : Set G)) {q : ℕ} [Fact q.Prime] (hi : K.index = q) :
    ∃ Q : Subgroup G, IsClosed (Q : Set G) ∧ Procyclic Q ∧ IsProP q Q ∧ Supplements K Q := by
  letI : K.FiniteIndex := ⟨hi ▸ (Fact.out : q.Prime).ne_zero⟩
  letI : IsOpen (K : Set G) := K.isOpen_of_isClosed_of_finiteIndex hK
  letI : DiscreteTopology (G ⧸ K) := inferInstance
  have hc : Nat.card (G ⧸ K) = q := hi
  letI : IsCyclic (G ⧸ K) := isCyclic_of_prime_card hc
  obtain ⟨z, hz⟩ := IsCyclic.exists_generator (α := G ⧸ K)
  obtain ⟨P, hP⟩ := exists_sylowPro (G := G) q
  let π := QuotientGroup.mk' K
  obtain ⟨S, hS⟩ := sylowPro_map_surjective_finite P hP π
    continuous_quotient_mk' (QuotientGroup.mk'_surjective K)
  have ht : S.toSubgroup = ⊤ := (S.is_maximal'
    ((IsPGroup.of_card (p := q) (n := 1) (by simpa using hc)).to_subgroup ⊤) le_top).symm
  have hzP : z ∈ P.map π := by rw [hS, ht]; trivial
  obtain ⟨x, hx, hπx⟩ := hzP
  let Q := (Subgroup.zpowers x).topologicalClosure
  have hQP : Q ≤ P := (Subgroup.zpowers x).topologicalClosure_minimal
    (Subgroup.zpowers_le.mpr hx) hP.2.1
  refine ⟨Q, (Subgroup.zpowers x).isClosed_topologicalClosure,
    procyclic_zpowers_closure x, isProP_mono hQP hP.2.2.1, ?_⟩
  intro g
  obtain ⟨n, hn⟩ := hz (π g)
  refine ⟨g * (x ^ n)⁻¹, ?_, x ^ n,
    (Subgroup.zpowers x).le_topologicalClosure (Subgroup.zpow_mem_zpowers x n), by group⟩
  rw [← QuotientGroup.eq_one_iff]
  change π (g * (x ^ n)⁻¹) = 1
  rw [map_mul, map_inv, map_zpow, hπx]
  change π g * (z ^ n)⁻¹ = 1
  change z ^ n = π g at hn
  rw [hn, mul_inv_cancel]

end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1

theorem solution :
∀ {G : Type u_1} [inst : Group.{u_1} G] [inst_1 : TopologicalSpace.{u_1} G]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} G inst inst_1] (K : @Subgroup.{u_1} G inst)
  [@Subgroup.Normal.{u_1} G inst K]
  (hK :
    @IsClosed.{u_1} G inst_1
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst) K))
  {q : Nat} [Fact (Nat.Prime q)] (hi : @Eq.{1} Nat (@Subgroup.index.{u_1} G inst K) q),
  @Exists.{u_1 + 1} (@Subgroup.{u_1} G inst) fun (Q : @Subgroup.{u_1} G inst) =>
    And
      (@IsClosed.{u_1} G inst_1
        (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst) Q))
      (And
        (@LocalConjugacy.Proof.LocalConjugacy.Procyclic.{u_1}
          (@Subtype.{u_1 + 1} G fun (x : G) =>
            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) Q x)
          (@Subgroup.toGroup.{u_1} G inst Q)
          (@instTopologicalSpaceSubtype.{u_1} G
            (fun (x : G) =>
              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) Q
                x)
            inst_1))
        (And
          (@LocalConjugacy.Proof.LocalConjugacy.IsProP.{u_1} q
            (@Subtype.{u_1 + 1} G fun (x : G) =>
              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) Q
                x)
            (@Subgroup.toGroup.{u_1} G inst Q)
            (@instTopologicalSpaceSubtype.{u_1} G
              (fun (x : G) =>
                @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) Q
                  x)
              inst_1))
          (@LocalConjugacy.Proof.LocalConjugacy.Supplements.{u_1} G inst K Q))) :=
  @LocalConjugacy.Proof.LocalConjugacy.exists_procyclic_supplement_preparedProof
