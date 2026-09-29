-- Prove2me | solution 1 for GoodReductionJacobian.BareDeformation.exists_factor_inf_of_local_lifts_factor_bare
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/53bd1099-50da-5a3f-85a8-b831e8b99ea9

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_IsRegluingBy
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import Definitions.Def_Algebra_PointDerivations
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_BareDeformation_exists_factor_inf_of_local_lifts_factor_bare

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal IsLocalRing AlgebraicGeometry.Scheme.TwoAffineOpenCover"

open scoped Quaternion TensorProduct NumberField

set_option maxHeartbeats 3200000 in
theorem solution
    (B B₁ : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B]
    [CommRing B₁] [Algebra B B₁]
    (hπ : Function.Surjective (algebraMap B B₁))
    (hI : RingHom.ker (algebraMap B B₁) ≤ maximalIdeal B)
    {A₁ : Scheme.{0}} (f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)) (L₁ : RelativeGroupLaw B₁ f₁)
    (D₀ : BareDeformation f₁ L₁ B) (𝒰 : D₀.A.OrderedAffineCover)
    (φ₁ : A₁ ⟶ A₁)

    (m : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ D₀.A)
    (hmμ : ∀ i, morphismRestrict D₀.g (𝒰.U i) ≫ m i = (D₀.g ⁻¹ᵁ (𝒰.U i)).ι ≫ φ₁ ≫ D₀.g)

    (D : BareDeformation f₁ L₁ B)
    (ιD : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ D.A)
    (hιg : ∀ i, (D₀.g ∣_ 𝒰.U i) ≫ ιD i = (D₀.g ⁻¹ᵁ 𝒰.U i).ι ≫ D.g)

    (mp : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ D.A)
    (hmpμ : ∀ i, morphismRestrict D₀.g (𝒰.U i) ≫ mp i = (D₀.g ⁻¹ᵁ (𝒰.U i)).ι ≫ φ₁ ≫ D.g)

    (i i' j j' : 𝒰.ι) (W₀ W₁ : D₀.A.Opens) (h₀ : W₀ ≤ 𝒰.U j) (h₁ : W₁ ≤ 𝒰.U j')
    (n₀ n₀' : (↑W₀ : Scheme.{0}) ⟶ ↑(𝒰.U i)) (n₁ n₁' : (↑W₁ : Scheme.{0}) ⟶ ↑(𝒰.U i'))
    (hn₀ : n₀ ≫ (𝒰.U i).ι = D₀.A.homOfLE h₀ ≫ m j) (hn₀' : n₀' ≫ ιD i = D₀.A.homOfLE h₀ ≫ mp j)
    (hn₁ : n₁ ≫ (𝒰.U i').ι = D₀.A.homOfLE h₁ ≫ m j') (hn₁' : n₁' ≫ ιD i' = D₀.A.homOfLE h₁ ≫ mp j') :
    ∃ (p p' q q' : (↑(W₀ ⊓ W₁) : Scheme.{0}) ⟶ ↑(𝒰.U i ⊓ 𝒰.U i')),
      p ≫ D₀.A.homOfLE inf_le_left = D₀.A.homOfLE inf_le_left ≫ n₀ ∧
      p' ≫ D₀.A.homOfLE inf_le_left = D₀.A.homOfLE inf_le_left ≫ n₀' ∧
      q ≫ D₀.A.homOfLE inf_le_right = D₀.A.homOfLE inf_le_right ≫ n₁ ∧
      q' ≫ D₀.A.homOfLE inf_le_right = D₀.A.homOfLE inf_le_right ≫ n₁' := by
  classical

  have hker : IsNilpotent (RingHom.ker (algebraMap B B₁)) := by
    obtain ⟨N, hN⟩ := (IsArtinianRing.isNilpotent_jacobson_bot (R := B))
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hN
    refine ⟨N, ?_⟩
    have h := (Ideal.pow_right_mono hI N).trans hN.le
    exact le_antisymm h bot_le
  have hSpecSurj : ∀ P : Spec (CommRingCat.of B), ∃ Q : Spec (CommRingCat.of B₁),
      (Spec.map (CommRingCat.ofHom (algebraMap B B₁))).base Q = P := by
    intro P
    obtain ⟨N, hN⟩ := hker
    have hle : (RingHom.ker (algebraMap B B₁) : Set B) ⊆ P.asIdeal := by
      intro x hx
      have hxN : x ^ N ∈ (RingHom.ker (algebraMap B B₁)) ^ N := Ideal.pow_mem_pow hx N
      rw [hN] at hxN
      have h0 : x ^ N = 0 := by simpa using hxN
      exact P.isPrime.mem_of_pow_mem N (by rw [h0]; exact zero_mem _)
    have hP : P ∈ Set.range (PrimeSpectrum.comap (algebraMap B B₁)) := by
      rw [range_comap_of_surjective _ (algebraMap B B₁) hπ]
      exact hle
    obtain ⟨Q, hQ⟩ := hP
    exact ⟨Q, hQ⟩
  have hgsurj : ∀ x : D₀.A, ∃ a : A₁, D₀.g.base a = x := by
    intro x
    obtain ⟨Q, hQ⟩ := hSpecSurj (D₀.f.base x)
    have hx : x ∈ Set.range (pullback.fst D₀.f (Spec.map (CommRingCat.ofHom (algebraMap B B₁)))).base := by
      rw [Scheme.Pullback.range_fst]
      exact ⟨Q, hQ⟩
    obtain ⟨p, hp⟩ := hx
    refine ⟨(D₀.cart.isoPullback).inv.base p, ?_⟩
    have := D₀.cart.isoPullback_inv_fst
    show ((D₀.cart.isoPullback).inv ≫ D₀.g).base p = x
    rw [this]
    exact hp

  have hm_pt : ∀ (j : 𝒰.ι) (a : A₁) (ha : D₀.g.base a ∈ 𝒰.U j),
      (m j).base ((D₀.g ∣_ 𝒰.U j).base ⟨a, ha⟩) = D₀.g.base (φ₁.base a) := by
    intro j a ha
    have := congrArg (fun φ => φ.base (⟨a, ha⟩ : ↥(D₀.g ⁻¹ᵁ 𝒰.U j))) (hmμ j)
    simpa [Scheme.Hom.comp_apply] using this
  have hmp_pt : ∀ (j : 𝒰.ι) (a : A₁) (ha : D₀.g.base a ∈ 𝒰.U j),
      (mp j).base ((D₀.g ∣_ 𝒰.U j).base ⟨a, ha⟩) = D.g.base (φ₁.base a) := by
    intro j a ha
    have := congrArg (fun φ => φ.base (⟨a, ha⟩ : ↥(D₀.g ⁻¹ᵁ 𝒰.U j))) (hmpμ j)
    simpa [Scheme.Hom.comp_apply] using this
  have hιD_pt : ∀ (i : 𝒰.ι) (a : A₁) (ha : D₀.g.base a ∈ 𝒰.U i),
      (ιD i).base ((D₀.g ∣_ 𝒰.U i).base ⟨a, ha⟩) = D.g.base a := by
    intro i a ha
    have := congrArg (fun φ => φ.base (⟨a, ha⟩ : ↥(D₀.g ⁻¹ᵁ 𝒰.U i))) (hιg i)
    simpa [Scheme.Hom.comp_apply] using this

  have hDg_inj : Function.Injective D.g.base := by
    haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap B B₁))) :=
      IsClosedImmersion.spec_of_surjective _ hπ
    haveI : IsClosedImmersion D.g :=
      MorphismProperty.of_isPullback (P := @IsClosedImmersion) D.cart.flip inferInstance
    exact D.g.isClosedEmbedding.injective

  have hres : ∀ (j : 𝒰.ι) (y : ↥(𝒰.U j)), ∃ (a : A₁) (ha : D₀.g.base a ∈ 𝒰.U j), (D₀.g ∣_ 𝒰.U j).base ⟨a, ha⟩ = y := by
    intro j y
    obtain ⟨a, ha⟩ := hgsurj y.1
    refine ⟨a, show D₀.g.base a ∈ 𝒰.U j by rw [ha]; exact y.2, ?_⟩
    apply Subtype.ext
    rw [morphismRestrict_base_coe]
    exact ha

  have key₀ : ∀ (z : ↥(W₀ ⊓ W₁)) (a : A₁), D₀.g.base a = z.1 →
      ((n₀.base ((D₀.A.homOfLE inf_le_left).base z)).1 = D₀.g.base (φ₁.base a)) ∧
      ((n₁.base ((D₀.A.homOfLE inf_le_right).base z)).1 = D₀.g.base (φ₁.base a)) := by
    intro z a ha
    constructor
    · have h := congrArg (fun φ => (φ.base ((D₀.A.homOfLE inf_le_left).base z) : D₀.A)) hn₀
      simp only [Scheme.Hom.comp_apply] at h
      rw [Scheme.Opens.ι_apply] at h
      rw [h]
      have hz : (D₀.A.homOfLE h₀).base ((D₀.A.homOfLE inf_le_left).base z) = (D₀.g ∣_ 𝒰.U j).base ⟨a, show D₀.g.base a ∈ 𝒰.U j by rw [ha]; exact h₀ (inf_le_left (a := W₀) (b := W₁) z.2)⟩ := by
        apply Subtype.ext
        rw [Scheme.homOfLE_apply, Scheme.homOfLE_apply, morphismRestrict_base_coe, ha]
      rw [hz, hm_pt]
    · have h := congrArg (fun φ => (φ.base ((D₀.A.homOfLE inf_le_right).base z) : D₀.A)) hn₁
      simp only [Scheme.Hom.comp_apply] at h
      rw [Scheme.Opens.ι_apply] at h
      rw [h]
      have hz : (D₀.A.homOfLE h₁).base ((D₀.A.homOfLE inf_le_right).base z) = (D₀.g ∣_ 𝒰.U j').base ⟨a, show D₀.g.base a ∈ 𝒰.U j' by rw [ha]; exact h₁ (inf_le_right (a := W₀) (b := W₁) z.2)⟩ := by
        apply Subtype.ext
        rw [Scheme.homOfLE_apply, Scheme.homOfLE_apply, morphismRestrict_base_coe, ha]
      rw [hz, hm_pt]

  have key₁ : ∀ (z : ↥(W₀ ⊓ W₁)) (a : A₁), D₀.g.base a = z.1 →
      ((n₀'.base ((D₀.A.homOfLE inf_le_left).base z)).1 = D₀.g.base (φ₁.base a)) ∧
      ((n₁'.base ((D₀.A.homOfLE inf_le_right).base z)).1 = D₀.g.base (φ₁.base a)) := by
    intro z a ha
    constructor
    · obtain ⟨a', ha', hy⟩ := hres i (n₀'.base ((D₀.A.homOfLE inf_le_left).base z))
      have h := congrArg (fun φ => (φ.base ((D₀.A.homOfLE inf_le_left).base z) : D.A)) hn₀'
      simp only [Scheme.Hom.comp_apply] at h
      have hz : (D₀.A.homOfLE h₀).base ((D₀.A.homOfLE inf_le_left).base z) = (D₀.g ∣_ 𝒰.U j).base ⟨a, show D₀.g.base a ∈ 𝒰.U j by rw [ha]; exact h₀ (inf_le_left (a := W₀) (b := W₁) z.2)⟩ := by
        apply Subtype.ext
        rw [Scheme.homOfLE_apply, Scheme.homOfLE_apply, morphismRestrict_base_coe, ha]
      rw [hz, hmp_pt, ← hy, hιD_pt] at h
      have haa : a' = φ₁.base a := hDg_inj h
      rw [← hy, morphismRestrict_base_coe]
      show D₀.g.base a' = _
      rw [haa]
    · obtain ⟨a', ha', hy⟩ := hres i' (n₁'.base ((D₀.A.homOfLE inf_le_right).base z))
      have h := congrArg (fun φ => (φ.base ((D₀.A.homOfLE inf_le_right).base z) : D.A)) hn₁'
      simp only [Scheme.Hom.comp_apply] at h
      have hz : (D₀.A.homOfLE h₁).base ((D₀.A.homOfLE inf_le_right).base z) = (D₀.g ∣_ 𝒰.U j').base ⟨a, show D₀.g.base a ∈ 𝒰.U j' by rw [ha]; exact h₁ (inf_le_right (a := W₀) (b := W₁) z.2)⟩ := by
        apply Subtype.ext
        rw [Scheme.homOfLE_apply, Scheme.homOfLE_apply, morphismRestrict_base_coe, ha]
      rw [hz, hmp_pt, ← hy, hιD_pt] at h
      have haa : a' = φ₁.base a := hDg_inj h
      rw [← hy, morphismRestrict_base_coe]
      show D₀.g.base a' = _
      rw [haa]

  have hrangeL : ∀ y : ↥(𝒰.U i), y.1 ∈ 𝒰.U i' → y ∈ Set.range (D₀.A.homOfLE (inf_le_left : 𝒰.U i ⊓ 𝒰.U i' ≤ 𝒰.U i)).base :=
    fun y hy => ⟨⟨y.1, ⟨y.2, hy⟩⟩, Subtype.ext (Scheme.homOfLE_apply _ _)⟩
  have hrangeR : ∀ y : ↥(𝒰.U i'), y.1 ∈ 𝒰.U i → y ∈ Set.range (D₀.A.homOfLE (inf_le_right : 𝒰.U i ⊓ 𝒰.U i' ≤ 𝒰.U i')).base :=
    fun y hy => ⟨⟨y.1, ⟨hy, y.2⟩⟩, Subtype.ext (Scheme.homOfLE_apply _ _)⟩
  have hp : Set.range (D₀.A.homOfLE (inf_le_left : W₀ ⊓ W₁ ≤ W₀) ≫ n₀).base ⊆
      Set.range (D₀.A.homOfLE (inf_le_left : 𝒰.U i ⊓ 𝒰.U i' ≤ 𝒰.U i)).base := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨a, ha⟩ := hgsurj z.1
    refine hrangeL _ ?_
    show (n₀.base ((D₀.A.homOfLE inf_le_left).base z)).1 ∈ 𝒰.U i'
    rw [(key₀ z a ha).1, ← (key₀ z a ha).2]
    exact (n₁.base _).2
  have hp' : Set.range (D₀.A.homOfLE (inf_le_left : W₀ ⊓ W₁ ≤ W₀) ≫ n₀').base ⊆
      Set.range (D₀.A.homOfLE (inf_le_left : 𝒰.U i ⊓ 𝒰.U i' ≤ 𝒰.U i)).base := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨a, ha⟩ := hgsurj z.1
    refine hrangeL _ ?_
    show (n₀'.base ((D₀.A.homOfLE inf_le_left).base z)).1 ∈ 𝒰.U i'
    rw [(key₁ z a ha).1, ← (key₀ z a ha).2]
    exact (n₁.base _).2
  have hq : Set.range (D₀.A.homOfLE (inf_le_right : W₀ ⊓ W₁ ≤ W₁) ≫ n₁).base ⊆
      Set.range (D₀.A.homOfLE (inf_le_right : 𝒰.U i ⊓ 𝒰.U i' ≤ 𝒰.U i')).base := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨a, ha⟩ := hgsurj z.1
    refine hrangeR _ ?_
    show (n₁.base ((D₀.A.homOfLE inf_le_right).base z)).1 ∈ 𝒰.U i
    rw [(key₀ z a ha).2, ← (key₀ z a ha).1]
    exact (n₀.base _).2
  have hq' : Set.range (D₀.A.homOfLE (inf_le_right : W₀ ⊓ W₁ ≤ W₁) ≫ n₁').base ⊆
      Set.range (D₀.A.homOfLE (inf_le_right : 𝒰.U i ⊓ 𝒰.U i' ≤ 𝒰.U i')).base := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨a, ha⟩ := hgsurj z.1
    refine hrangeR _ ?_
    show (n₁'.base ((D₀.A.homOfLE inf_le_right).base z)).1 ∈ 𝒰.U i
    rw [(key₁ z a ha).2, ← (key₀ z a ha).1]
    exact (n₀.base _).2
  exact ⟨IsOpenImmersion.lift _ _ hp, IsOpenImmersion.lift _ _ hp', IsOpenImmersion.lift _ _ hq, IsOpenImmersion.lift _ _ hq',
    IsOpenImmersion.lift_fac _ _ _, IsOpenImmersion.lift_fac _ _ _, IsOpenImmersion.lift_fac _ _ _,
    IsOpenImmersion.lift_fac _ _ _⟩

end S_GoodReductionJacobian_BareDeformation_exists_factor_inf_of_local_lifts_factor_bare
end P2MW
export P2MW.S_GoodReductionJacobian_BareDeformation_exists_factor_inf_of_local_lifts_factor_bare (solution)
