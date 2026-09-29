-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.exists_ringEquiv_adicCompletion_uvCrossingModel_pow_of_isInvariant_of_isLocalization_atPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/5ec39d76-3e4b-5213-abb8-89fc5ebf76f3

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_InvariantBaseChange
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_ringEquiv_adicCompletion_uvCrossingModel_pow_of_isInvariant_of_card_inertia_eq_of_isUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_exists_ringEquiv_adicCompletion_uvCrossingModel_pow_of_isInvariant_of_isLocalization_atPrime
p2m_attr_erase "instance" "AdicCompletion.instIsLocalRingMaximalIdeal instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "AdicCompletion.map_smul_of AdicCompletion.algebraMap_of AdicCompletion.stabilizer_smul_of AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul"

set_option autoImplicit false

open scoped Pointwise TensorProduct
open IsLocalRing ModularCurve ModularCurve.UVCrossingModel

namespace IsLocalization p2m_export "IsLocalization" "surj under_map_of_isPrime_disjoint isNoetherianRing map map_units AtPrime.map_eq_maximalIdeal localization_isScalarTower_of_submonoid_le AtPrime.comap_maximalIdeal flat isPrime_of_isPrime_disjoint isDomain_of_le_nonZeroDivisors map_under isLocalization_of_is_exists_mul_mem localizationAlgebraOfSubmonoidLe tensorRight ringHom_ext isLocalization_of_submonoid_le" end IsLocalization
p2m_open_scoped "IsLocalization" in
open _root_.IsLocalization in

theorem IsLocalization.isLocalization_atPrime_of_isLocalization_of_atPrime_comap
    {A : Type*} [CommRing A] (M : Submonoid A)
    (C : Type*) [CommRing C] [Algebra A C] [IsLocalization M C]
    (𝔫 : Ideal C) [𝔫.IsPrime] (𝔭 : Ideal A) [𝔭.IsPrime] (h𝔭 : 𝔫.comap (algebraMap A C) = 𝔭)
    (T : Type*) [CommRing T] [Algebra A T] [IsLocalization.AtPrime T 𝔭]
    [Algebra C T] [IsScalarTower A C T] :
    IsLocalization.AtPrime T 𝔫 := by
  subst h𝔭
  have hM : M ≤ (𝔫.comap (algebraMap A C)).primeCompl := by
    intro m hm hm𝔫
    exact (inferInstance : 𝔫.IsPrime).ne_top (𝔫.eq_top_of_isUnit_mem hm𝔫 (IsLocalization.map_units C ⟨m, hm⟩))
  have h1 : IsLocalization (((𝔫.comap (algebraMap A C)).primeCompl).map (algebraMap A C)) T :=
    isLocalization_of_submonoid_le C T M (𝔫.comap (algebraMap A C)).primeCompl hM
  refine isLocalization_of_is_exists_mul_mem T
    (((𝔫.comap (algebraMap A C)).primeCompl).map (algebraMap A C)) 𝔫.primeCompl ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    exact ha
  · rintro ⟨x, hx⟩
    obtain ⟨⟨a, s⟩, e⟩ := IsLocalization.surj M x
    dsimp only at e
    refine ⟨algebraMap A C s, ?_⟩
    refine ⟨a, ?_, by rw [mul_comm]; exact e.symm⟩
    intro ha
    apply hx
    have hmem : x * algebraMap A C s ∈ 𝔫 := by
      rw [e]; exact ha
    exact ((inferInstance : 𝔫.IsPrime).mem_or_mem hmem).resolve_right (fun hs => (hM s.2) hs)

theorem FloorRC.quotientMap_surjective_of_isLocalization
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (M : Submonoid R) [IsLocalization M S]
    (I : Ideal R) [hI : I.IsMaximal] (J : Ideal S) (hJ : J ≠ ⊤) (h : I ≤ J.comap (algebraMap R S)) :
    Function.Surjective (Ideal.quotientMap J (algebraMap R S) h) := by
  classical
  letI := Ideal.Quotient.field I
  intro q
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨⟨r, s⟩, hx⟩ := IsLocalization.surj M x
  have hs : (Ideal.Quotient.mk I (s : R)) ≠ 0 := by
    intro h0
    rw [Ideal.Quotient.eq_zero_iff_mem] at h0
    exact hJ (J.eq_top_of_isUnit_mem (Ideal.mem_comap.mp (h h0)) (IsLocalization.map_units S s))
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective ((Ideal.Quotient.mk I (s : R))⁻¹)
  have hst : (s : R) * t - 1 ∈ I := by
    rw [← Ideal.Quotient.eq, map_mul, ht, map_one]
    exact mul_inv_cancel₀ hs
  refine ⟨Ideal.Quotient.mk I (r * t), ?_⟩
  rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
  have : algebraMap R S (r * t) - x = x * algebraMap R S ((s : R) * t - 1) := by
    rw [map_mul, map_sub, map_mul, map_one, mul_sub, mul_one, ← mul_assoc, hx]
  rw [this]
  exact J.mul_mem_left _ (Ideal.mem_comap.mp (h hst))

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem solution
    {A₂ A₁ : Type} [CommRing A₂] [CommRing A₁] [IsNoetherianRing A₂] [IsNoetherianRing A₁] [IsDomain A₁]
    [Algebra A₂ A₁] [Module.Finite A₂ A₁] [FaithfulSMul A₂ A₁]
    {G : Type} [Group G] [Fintype G] [MulSemiringAction G A₁] [SMulCommClass G A₂ A₁] [FaithfulSMul G A₁]
    [Algebra.IsInvariant A₂ A₁ G]
    (y : Ideal A₁) [y.IsMaximal] (𝔭 : Ideal A₂) [𝔭.IsPrime] (h𝔭 : y.comap (algebraMap A₂ A₁) = 𝔭)
    {W₂ : Type} [CommRing W₂] [IsDomain W₂] [IsDiscreteValuationRing W₂] [IsAdicComplete (maximalIdeal W₂) W₂]
    (π : W₂) (hπ : Irreducible π) (m w : ℕ) (hm : 0 < m) (hw : 0 < w) (hwW : IsUnit (w : W₂))
    (hmW : IsUnit (m : W₂))
    (hIy : Nat.card ↥(y.inertia G) = w) (hIcyc : IsCyclic ↥(y.inertia G))
    (O : Type) [CommRing O] [IsLocalRing O] [Algebra A₂ O] [IsLocalization.AtPrime O 𝔭]
    (eO : AdicCompletion (maximalIdeal O) O ≃+* UVCrossingModel W₂ (π ^ (m * w)))
    (S : Type) [CommRing S] [IsLocalRing S] [Algebra A₁ S] [IsLocalization.AtPrime S y]
    (hSdom : IsDomain (AdicCompletion (maximalIdeal S) S))
    (hSnorm : IsIntegrallyClosed (AdicCompletion (maximalIdeal S) S))

    (hunr : letI : Algebra A₂ S := ((algebraMap A₁ S).comp (algebraMap A₂ A₁)).toAlgebra
      ∀ (𝔮 : Ideal S) [𝔮.IsPrime], ¬ 𝔮.IsMaximal → Algebra.IsUnramifiedAt A₂ 𝔮)

    (hsep : ∀ h : 𝔭 ≤ y.comap (algebraMap A₂ A₁),
      letI : Algebra (A₂ ⧸ 𝔭) (A₁ ⧸ y) := Ideal.Quotient.algebraQuotientOfLEComap h
      Algebra.IsSeparable (A₂ ⧸ 𝔭) (A₁ ⧸ y)) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : IsAdicComplete (maximalIdeal W) W) (σ : W₂ →+* W)
      (_ : maximalIdeal W = Ideal.span {σ π})
      (e : AdicCompletion (maximalIdeal S) S ≃+* UVCrossingModel W ((σ π) ^ m)),
      ∀ (b : A₂) (w₀ : W₂), eO (algebraMap O (AdicCompletion (maximalIdeal O) O) (algebraMap A₂ O b)) = const (π ^ (m * w)) w₀ →
        e (algebraMap S (AdicCompletion (maximalIdeal S) S) (algebraMap A₁ S (algebraMap A₂ A₁ b))) = const ((σ π) ^ m) (σ w₀)  := by
  classical
  letI algA₂S : Algebra A₂ S := ((algebraMap A₁ S).comp (algebraMap A₂ A₁)).toAlgebra
  haveI : IsScalarTower A₂ A₁ S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsNoetherianRing O := IsLocalization.isNoetherianRing 𝔭.primeCompl O inferInstance
  haveI : Module.Flat A₂ O := IsLocalization.flat O 𝔭.primeCompl
  have hMle : Algebra.algebraMapSubmonoid A₁ 𝔭.primeCompl ≤ y.primeCompl := by
    rintro _ ⟨b, hb, rfl⟩ hby
    exact hb (by rw [← h𝔭]; exact hby)

  have hMnz : Algebra.algebraMapSubmonoid A₁ 𝔭.primeCompl ≤ nonZeroDivisors A₁ := by
    rintro _ ⟨b, hb, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero (fun h0 => hb ?_)
    have : b = 0 := (faithfulSMul_iff_algebraMap_injective A₂ A₁).mp inferInstance (by rw [h0, map_zero])
    rw [this]; exact 𝔭.zero_mem
  haveI : IsDomain (O ⊗[A₂] A₁) := IsLocalization.isDomain_of_le_nonZeroDivisors (O ⊗[A₂] A₁) hMnz
  haveI : FaithfulSMul O (O ⊗[A₂] A₁) := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (Algebra.TensorProduct.includeLeft_injective (S := O) ((faithfulSMul_iff_algebraMap_injective A₂ A₁).mp inferInstance))
  letI : MulSemiringAction G (O ⊗[A₂] A₁) := Algebra.TensorProduct.rightMulSemiringAction A₂ O A₁ G
  haveI : SMulCommClass G O (O ⊗[A₂] A₁) := Algebra.TensorProduct.rightMulSemiringAction_smulCommClass A₂ O A₁ G
  haveI : Algebra.IsInvariant O (O ⊗[A₂] A₁) G := Algebra.IsInvariant.isInvariant_tensorProduct_of_flat A₂ O A₁ G
  haveI : FaithfulSMul G (O ⊗[A₂] A₁) := ⟨fun {g₁ g₂} h => FaithfulSMul.eq_of_smul_eq_smul (α := A₁) (fun a => by
    apply IsLocalization.injective (O ⊗[A₂] A₁) hMnz
    have := h ((1 : O) ⊗ₜ[A₂] a)
    rw [Algebra.TensorProduct.rightMulSemiringAction_smul_tmul, Algebra.TensorProduct.rightMulSemiringAction_smul_tmul] at this
    exact this)⟩

  obtain ⟨𝔫, h𝔫def⟩ : ∃ 𝔫 : Ideal (O ⊗[A₂] A₁), 𝔫 = y.map (algebraMap A₁ (O ⊗[A₂] A₁)) := ⟨_, rfl⟩
  have hdisj : Disjoint (↑(Algebra.algebraMapSubmonoid A₁ 𝔭.primeCompl) : Set A₁) ↑y := by
    rw [Set.disjoint_left]
    rintro _ ⟨b, hb, rfl⟩ hby
    exact hb (by rw [← h𝔭]; exact hby)
  have h𝔫comap : 𝔫.comap (algebraMap A₁ (O ⊗[A₂] A₁)) = y := by
    rw [h𝔫def]
    exact IsLocalization.under_map_of_isPrime_disjoint (Algebra.algebraMapSubmonoid A₁ 𝔭.primeCompl) (O ⊗[A₂] A₁)
      (I := y) inferInstance hdisj
  haveI : 𝔫.IsPrime := by
    rw [h𝔫def]
    exact IsLocalization.isPrime_of_isPrime_disjoint (Algebra.algebraMapSubmonoid A₁ 𝔭.primeCompl) _ y inferInstance hdisj
  haveI h𝔫max : 𝔫.IsMaximal := by
    refine ⟨⟨Ideal.IsPrime.ne_top inferInstance, fun J hJ => ?_⟩⟩
    by_contra hJtop
    have h1 : y ≤ J.comap (algebraMap A₁ (O ⊗[A₂] A₁)) := by rw [← h𝔫comap]; exact Ideal.comap_mono hJ.le
    have h2 : J.comap (algebraMap A₁ (O ⊗[A₂] A₁)) ≠ ⊤ := fun h => hJtop (Ideal.comap_eq_top_iff.mp h)
    have h3 : y = J.comap (algebraMap A₁ (O ⊗[A₂] A₁)) := (inferInstance : y.IsMaximal).eq_of_le h2 h1
    apply hJ.ne
    rw [h𝔫def, h3]
    exact IsLocalization.map_under (Algebra.algebraMapSubmonoid A₁ 𝔭.primeCompl) (O ⊗[A₂] A₁) J
  haveI : 𝔫.LiesOver (maximalIdeal O) := by
    refine ⟨(IsLocalRing.maximalIdeal.isMaximal O).eq_of_le
      (Ideal.comap_ne_top _ (Ideal.IsMaximal.ne_top inferInstance)) ?_⟩
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal 𝔭 O, Ideal.map_le_iff_le_comap]
    intro b hb
    have hb' : algebraMap A₂ A₁ b ∈ y := by rw [← Ideal.mem_comap, h𝔭]; exact hb
    show algebraMap O (O ⊗[A₂] A₁) (algebraMap A₂ O b) ∈ 𝔫
    rw [← IsScalarTower.algebraMap_apply A₂ O (O ⊗[A₂] A₁), IsScalarTower.algebraMap_apply A₂ A₁ (O ⊗[A₂] A₁), h𝔫def]
    exact Ideal.mem_map_of_mem _ hb'

  letI algCS : Algebra (O ⊗[A₂] A₁) S :=
    IsLocalization.localizationAlgebraOfSubmonoidLe (O ⊗[A₂] A₁) S (Algebra.algebraMapSubmonoid A₁ 𝔭.primeCompl) y.primeCompl hMle
  haveI : IsScalarTower A₁ (O ⊗[A₂] A₁) S :=
    IsLocalization.localization_isScalarTower_of_submonoid_le (O ⊗[A₂] A₁) S (Algebra.algebraMapSubmonoid A₁ 𝔭.primeCompl) y.primeCompl hMle
  haveI : IsLocalization.AtPrime S 𝔫 :=
    IsLocalization.isLocalization_atPrime_of_isLocalization_of_atPrime_comap
      (Algebra.algebraMapSubmonoid A₁ 𝔭.primeCompl) (O ⊗[A₂] A₁) 𝔫 y h𝔫comap S
  letI algOS : Algebra O S := ((algebraMap (O ⊗[A₂] A₁) S).comp (algebraMap O (O ⊗[A₂] A₁))).toAlgebra
  haveI : IsScalarTower O (O ⊗[A₂] A₁) S := ⟨fun o c s => by
    rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul, mul_assoc]; rfl⟩
  have hOS' : ∀ b : A₂, algebraMap O S (algebraMap A₂ O b) = algebraMap A₁ S (algebraMap A₂ A₁ b) := fun b => by
    show algebraMap (O ⊗[A₂] A₁) S (algebraMap O (O ⊗[A₂] A₁) (algebraMap A₂ O b)) = _
    rw [← IsScalarTower.algebraMap_apply A₂ O (O ⊗[A₂] A₁) b, IsScalarTower.algebraMap_apply A₂ A₁ (O ⊗[A₂] A₁) b,
      ← IsScalarTower.algebraMap_apply A₁ (O ⊗[A₂] A₁) S]
  haveI : IsScalarTower A₂ O S := IsScalarTower.of_algebraMap_eq (fun b => (hOS' b).symm ▸ rfl)
  have hunrO : ∀ (𝔮 : Ideal S) [𝔮.IsPrime], ¬ 𝔮.IsMaximal → Algebra.IsUnramifiedAt O 𝔮 := by
    intro 𝔮 _ h𝔮
    haveI : Algebra.FormallyUnramified A₂ (Localization.AtPrime 𝔮) := hunr 𝔮 h𝔮
    haveI : IsScalarTower A₂ O (Localization.AtPrime 𝔮) := IsScalarTower.of_algebraMap_eq (fun b => by
      rw [IsScalarTower.algebraMap_apply O S (Localization.AtPrime 𝔮), IsScalarTower.algebraMap_apply A₂ S (Localization.AtPrime 𝔮),
        IsScalarTower.algebraMap_apply A₂ O S])
    exact Algebra.FormallyUnramified.of_restrictScalars A₂ O (Localization.AtPrime 𝔮)

  have hinert : 𝔫.inertia G = y.inertia G := by
    ext g
    constructor
    · intro hg a
      have h1 : g • algebraMap A₁ (O ⊗[A₂] A₁) a - algebraMap A₁ (O ⊗[A₂] A₁) a ∈ 𝔫 := hg _
      show g • a - a ∈ y
      rw [← h𝔫comap, Ideal.mem_comap, map_sub]
      have h2 : g • algebraMap A₁ (O ⊗[A₂] A₁) a = algebraMap A₁ (O ⊗[A₂] A₁) (g • a) := by
        show g • ((1 : O) ⊗ₜ[A₂] a) = (1 : O) ⊗ₜ[A₂] (g • a)
        rw [Algebra.TensorProduct.rightMulSemiringAction_smul_tmul]
      rwa [h2] at h1
    · intro hg c
      show g • c - c ∈ 𝔫
      induction c using TensorProduct.induction_on with
      | zero => rw [smul_zero, sub_zero]; exact Ideal.zero_mem _
      | tmul o a =>
        rw [Algebra.TensorProduct.rightMulSemiringAction_smul_tmul, ← TensorProduct.tmul_sub]
        have hmem : (1 : O) ⊗ₜ[A₂] (g • a - a) ∈ 𝔫 := by rw [h𝔫def]; exact Ideal.mem_map_of_mem _ (hg a)
        have : o ⊗ₜ[A₂] (g • a - a) = (o ⊗ₜ[A₂] (1 : A₁)) * ((1 : O) ⊗ₜ[A₂] (g • a - a)) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        rw [this]; exact Ideal.mul_mem_left _ _ hmem
      | add x x' hx hx' => rw [smul_add, add_sub_add_comm]; exact Ideal.add_mem _ hx hx'
  have hI : Nat.card ↥((𝔫.inertia G).subgroupOf (MulAction.stabilizer G 𝔫)) = w := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Ideal.inertia_le_stabilizer 𝔫)).toEquiv, hinert]; exact hIy
  have hIcyc' : IsCyclic ↥(𝔫.inertia G) := by rw [hinert]; exact hIcyc
  haveI : Algebra.IsSeparable (O ⧸ maximalIdeal O) ((O ⊗[A₂] A₁) ⧸ 𝔫) := by

    haveI : Algebra.IsIntegral A₂ A₁ := inferInstance
    haveI h𝔭max : 𝔭.IsMaximal := h𝔭 ▸ Ideal.isMaximal_comap_of_isIntegral_of_isMaximal y
    have hle : 𝔭 ≤ y.comap (algebraMap A₂ A₁) := h𝔭 ▸ le_rfl
    haveI hsep' := hsep hle
    letI algQ : Algebra (A₂ ⧸ 𝔭) (A₁ ⧸ y) := Ideal.Quotient.algebraQuotientOfLEComap hle
    letI := Ideal.Quotient.field 𝔭
    letI := Ideal.Quotient.field y
    letI := Ideal.Quotient.field (maximalIdeal O)
    letI := Ideal.Quotient.field 𝔫
    have hle₁ : 𝔭 ≤ (maximalIdeal O).comap (algebraMap A₂ O) :=
      (IsLocalization.AtPrime.comap_maximalIdeal (I := 𝔭) O).symm ▸ le_rfl
    have hle₂ : y ≤ 𝔫.comap (algebraMap A₁ (O ⊗[A₂] A₁)) := h𝔫comap ▸ le_rfl
    let e₁ : (A₂ ⧸ 𝔭) ≃+* (O ⧸ maximalIdeal O) := RingEquiv.ofBijective (Ideal.quotientMap _ _ hle₁)
      ⟨RingHom.injective _, FloorRC.quotientMap_surjective_of_isLocalization 𝔭.primeCompl 𝔭 _ (Ideal.IsMaximal.ne_top inferInstance) hle₁⟩
    let e₂ : (A₁ ⧸ y) ≃+* ((O ⊗[A₂] A₁) ⧸ 𝔫) := RingEquiv.ofBijective (Ideal.quotientMap _ _ hle₂)
      ⟨RingHom.injective _, FloorRC.quotientMap_surjective_of_isLocalization (Algebra.algebraMapSubmonoid A₁ 𝔭.primeCompl) y _
        (Ideal.IsMaximal.ne_top inferInstance) hle₂⟩
    refine Algebra.IsSeparable.of_equiv_equiv e₁ e₂ ?_
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun b => ?_)
    show algebraMap (O ⧸ maximalIdeal O) ((O ⊗[A₂] A₁) ⧸ 𝔫) (Ideal.quotientMap _ _ hle₁ (Ideal.Quotient.mk 𝔭 b)) =
      Ideal.quotientMap _ _ hle₂ (algebraMap (A₂ ⧸ 𝔭) (A₁ ⧸ y) (Ideal.Quotient.mk 𝔭 b))
    have hR : algebraMap (A₂ ⧸ 𝔭) (A₁ ⧸ y) (Ideal.Quotient.mk 𝔭 b) = Ideal.Quotient.mk y (algebraMap A₂ A₁ b) := rfl
    rw [hR, Ideal.quotientMap_mk, Ideal.quotientMap_mk, Ideal.Quotient.algebraMap_mk_of_liesOver, Ideal.Quotient.eq]
    rw [← IsScalarTower.algebraMap_apply A₂ O (O ⊗[A₂] A₁), IsScalarTower.algebraMap_apply A₂ A₁ (O ⊗[A₂] A₁), sub_self]
    exact Ideal.zero_mem _
  obtain ⟨W, i1, i2, i3, i4, σ, hσ, e, he⟩ :=
    ModularCurve.UVCrossingModel.exists_ringEquiv_adicCompletion_uvCrossingModel_pow_of_isInvariant_of_card_inertia_eq_of_isUnit
      (O := O) (C := O ⊗[A₂] A₁) 𝔫 π hπ m w hm hw hwW hmW hI hIcyc' eO S hSdom hSnorm hunrO
  refine ⟨W, i1, i2, i3, i4, σ, hσ, e, fun b w₀ hb => ?_⟩
  have hOS : algebraMap O S (algebraMap A₂ O b) = algebraMap A₁ S (algebraMap A₂ A₁ b) := hOS' b
  rw [← hOS]
  exact he _ _ hb

end S_ModularCurve_UVCrossingModel_exists_ringEquiv_adicCompletion_uvCrossingModel_pow_of_isInvariant_of_isLocalization_atPrime
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_exists_ringEquiv_adicCompletion_uvCrossingModel_pow_of_isInvariant_of_isLocalization_atPrime (solution)
