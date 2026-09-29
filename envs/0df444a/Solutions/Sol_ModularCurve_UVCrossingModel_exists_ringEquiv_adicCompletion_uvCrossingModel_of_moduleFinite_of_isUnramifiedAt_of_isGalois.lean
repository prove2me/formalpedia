-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.exists_ringEquiv_adicCompletion_uvCrossingModel_of_moduleFinite_of_isUnramifiedAt_of_isGalois
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/96c8981f-2b4f-59bd-9056-8a0ef752a855

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AdicCompletionLocalRing
import Theorems.Thm_AdicCompletion_isNoetherianRing_of_isNoetherianRing
import Theorems.Thm_ModularCurve_UVCrossingModel_isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete
import Theorems.Thm_ModularCurve_UVCrossingModel_isNoetherianRing
import Theorems.Thm_ModularCurve_UVCrossingModel_ringKrullDim_le_two
import Theorems.Thm_IsLocalRing_exists_adicCompletion_ringHom_finite_of_moduleFinite
import Theorems.Thm_Algebra_IsUnramifiedAt_baseChange_of_ne_maximalIdeal_of_map_maximalIdeal_eq
import Theorems.Thm_Algebra_IsUnramifiedAt_isRegularLocalRing_localization_of_ne_maximalIdeal
import Theorems.Thm_IsIntegrallyClosed_isRegularLocalRing_localization_of_ne_maximalIdeal_of_ringKrullDim_le_two
import Theorems.Thm_IsLocalRing_ringKrullDim_adicCompletion_maximalIdeal_eq
import Theorems.Thm_IsLocalRing_isDomain_and_isIntegrallyClosed_and_isFractionRing_of_forall_not_isMaximal_isRegularLocalRing
import Theorems.Thm_IsIntegrallyClosed_exists_isRegular_pair_of_two_le_ringKrullDim
import Theorems.Thm_IsGalois_of_bijective_tensorProduct_lift
import Theorems.Thm_IsFractionRing_bijective_tensorProduct_lift_of_bijective_baseChange
import Theorems.Thm_IsLocalization_exists_algEquiv_tensorProduct_and_injective_of_bijective_baseChange
import Theorems.Thm_Algebra_IsSeparable_isReduced_and_isSeparable_and_finite_tensorProduct
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_ringEquiv_uvCrossingModel_of_isGalois_of_isCyclic_of_isUnramifiedAt_of_residue
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_sub_const_mem_maximalIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_exists_ringEquiv_adicCompletion_uvCrossingModel_of_moduleFinite_of_isUnramifiedAt_of_isGalois

set_option autoImplicit false

section
open ModularCurve ModularCurve.UVCrossingModel
open scoped TensorProduct

set_option maxHeartbeats 3200000 in
theorem solution
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (n : ℕ) (hn : 0 < n) (hnW : IsUnit (n : W))
    (hμ : ∃ ζ : W, IsPrimitiveRoot ζ n)
    (Sb S : Type*) [CommRing Sb] [CommRing S] [IsNoetherianRing Sb] [IsNoetherianRing S]
    [IsLocalRing Sb] [IsLocalRing S] [IsDomain S] [IsIntegrallyClosed S]
    [Algebra Sb S] [Module.Finite Sb S] (hinj : Function.Injective (algebraMap Sb S))
    (hdimS : ringKrullDim S ≤ (2 : WithBot ℕ∞)) (hdimS' : 2 ≤ ringKrullDim S) (hdimSb : 2 ≤ ringKrullDim Sb)
    (t : S) (ht : t ∈ IsLocalRing.maximalIdeal S) (ht0 : t ≠ 0)
    (hunrS : ∀ (𝔮 : Ideal S) [𝔮.IsPrime], ¬ 𝔮.IsMaximal → Algebra.IsUnramifiedAt Sb 𝔮)
    (hresS : ∀ s : S, ∃ r : Sb, s - algebraMap Sb S r ∈ IsLocalRing.maximalIdeal S)
    (eb : (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb) ≃+* UVCrossingModel W (π ^ n))
    (K₁ K : Type*) [Field K₁] [Field K] [Algebra Sb K₁] [IsFractionRing Sb K₁]
    [Algebra S K] [IsFractionRing S K] [Algebra K₁ K] [Algebra Sb K]
    [IsScalarTower Sb S K] [IsScalarTower Sb K₁ K] [FiniteDimensional K₁ K] [IsGalois K₁ K]
    (hcycK : IsCyclic (K ≃ₐ[K₁] K)) (hdegK : Module.finrank K₁ K = n) :
    ∃ e : (AdicCompletion (IsLocalRing.maximalIdeal S) S) ≃+* UVCrossingModel W π,
      ∀ (x : Sb) (w : W), eb (algebraMap Sb (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb) x) = const (π ^ n) w →
        e (algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) (algebraMap Sb S x)) = const π w := by
  classical
  haveI : IsNoetherianRing (AdicCompletion (IsLocalRing.maximalIdeal S) S) := AdicCompletion.isNoetherianRing_of_isNoetherianRing _
  haveI : IsNoetherianRing (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb) := AdicCompletion.isNoetherianRing_of_isNoetherianRing _
  haveI : IsDomain Sb := Function.Injective.isDomain (algebraMap Sb S) hinj

  obtain ⟨φh, hφh_comm, hφh_fin, hφh_inj', etens, hetens₁, hetens₂⟩ :=
    IsLocalRing.exists_adicCompletion_ringHom_finite_of_moduleFinite Sb S
  have hφh_inj : Function.Injective φh := hφh_inj' hinj

  have hcast₁ : uvCrossingIdeal W (π ^ n) = uvCrossingIdeal W (π ^ (1 * n)) := by rw [one_mul]
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : UVCrossingModel W (π ^ n) ≃+* (UVCrossingModel W (π ^ (1 * n))),
      ∀ f, c₁ (UVCrossingModel.mk (π ^ n) f) = UVCrossingModel.mk (π ^ (1 * n)) f :=
    ⟨Ideal.quotEquivOfEq hcast₁, fun f => rfl⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : (UVCrossingModel W (π ^ (1 * n))) →+* (AdicCompletion (IsLocalRing.maximalIdeal S) S), ∀ r, ψ r = φh (eb.symm (c₁.symm r)) :=
    ⟨φh.comp ((c₁.symm.trans eb.symm).toRingHom), fun r => rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : Sb →+* (UVCrossingModel W (π ^ (1 * n))), ∀ x, τ x = c₁ (eb (algebraMap Sb (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb) x)) :=
    ⟨(c₁ : UVCrossingModel W (π ^ n) →+* (UVCrossingModel W (π ^ (1 * n)))).comp ((eb : (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb) →+* _).comp (algebraMap Sb (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb))), fun x => rfl⟩
  have hψτ : ∀ x : Sb, ψ (τ x) = algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) (algebraMap Sb S x) := by
    intro x; rw [hψ, hτ, RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply, hφh_comm]
  have hτ_inj : Function.Injective τ := by
    intro a b h
    rw [hτ, hτ] at h
    exact AdicCompletion.of_injective (I := IsLocalRing.maximalIdeal Sb) (M := Sb) (eb.injective (c₁.injective h))
  letI algR0 : Algebra (UVCrossingModel W (π ^ (1 * n))) (AdicCompletion (IsLocalRing.maximalIdeal S) S) := ψ.toAlgebra
  letI algSbR0 : Algebra Sb (UVCrossingModel W (π ^ (1 * n))) := τ.toAlgebra

  haveI : IsScalarTower Sb S (AdicCompletion (IsLocalRing.maximalIdeal S) S) := by
    first | infer_instance | exact IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hSbŜ : ∀ x : Sb, algebraMap Sb (AdicCompletion (IsLocalRing.maximalIdeal S) S) x = algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) (algebraMap Sb S x) := fun x =>
    IsScalarTower.algebraMap_apply Sb S (AdicCompletion (IsLocalRing.maximalIdeal S) S) x
  haveI : IsScalarTower Sb (UVCrossingModel W (π ^ (1 * n))) (AdicCompletion (IsLocalRing.maximalIdeal S) S) := IsScalarTower.of_algebraMap_eq (fun x => by rw [hSbŜ]; exact (hψτ x).symm)
  have h1n : 1 ≤ 1 * n := by rw [Nat.one_mul]; exact hn
  haveI : IsDomain (UVCrossingModel W (π ^ (1 * n))) := (isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete π hπ (1 * n) h1n).1
  haveI : IsLocalRing (UVCrossingModel W (π ^ (1 * n))) := (isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete π hπ (1 * n) h1n).2.1
  haveI : IsIntegrallyClosed (UVCrossingModel W (π ^ (1 * n))) := (isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete π hπ (1 * n) h1n).2.2
  haveI : IsNoetherianRing (UVCrossingModel W (π ^ (1 * n))) := UVCrossingModel.isNoetherianRing _
  haveI : Module.Finite (UVCrossingModel W (π ^ (1 * n))) (AdicCompletion (IsLocalRing.maximalIdeal S) S) := by
    have hψfin : ψ.Finite := by
      rw [show ψ = φh.comp ((c₁.symm.trans eb.symm).toRingHom) from RingHom.ext hψ]
      exact hφh_fin.comp (RingHom.Finite.of_surjective _ (c₁.symm.trans eb.symm).surjective)
    exact hψfin
  haveI : FaithfulSMul (UVCrossingModel W (π ^ (1 * n))) (AdicCompletion (IsLocalRing.maximalIdeal S) S) := by
    refine (faithfulSMul_iff_algebraMap_injective _ _).mpr ?_
    intro a b h
    have h' : ψ a = ψ b := h
    rw [hψ, hψ] at h'
    exact c₁.symm.injective (eb.symm.injective (hφh_inj h'))

  have hmaxb : Ideal.map (algebraMap Sb (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb)) (IsLocalRing.maximalIdeal Sb) = IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb) := by
    first
      | exact (AdicCompletion.maximalIdeal_eq_map _).symm
      | exact AdicCompletion.maximalIdeal_eq_map.symm
      | exact (AdicCompletion.maximalIdeal_eq_map (A := Sb)).symm
  have hM5a := Algebra.IsUnramifiedAt.baseChange_of_ne_maximalIdeal_of_map_maximalIdeal_eq (R := Sb) (R' := (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb)) (S := S) hmaxb hunrS
  haveI : NoZeroSMulDivisors Sb S := ⟨fun {c x} h => by
    rw [Algebra.smul_def] at h
    rcases mul_eq_zero.mp h with h | h
    · left; exact hinj (by rw [h, map_zero])
    · right; exact h⟩
  have G39'_hT : Function.Bijective
      (Algebra.TensorProduct.lift (Algebra.ofId (UVCrossingModel W (π ^ (1 * n))) (AdicCompletion (IsLocalRing.maximalIdeal S) S)) (IsScalarTower.toAlgHom Sb S (AdicCompletion (IsLocalRing.maximalIdeal S) S))
        (fun _ _ => Commute.all _ _) : TensorProduct Sb (UVCrossingModel W (π ^ (1 * n))) S →ₐ[(UVCrossingModel W (π ^ (1 * n)))] (AdicCompletion (IsLocalRing.maximalIdeal S) S)) := by

    have hρcomm : ∀ x : Sb, (c₁.symm.trans eb.symm) (algebraMap Sb (UVCrossingModel W (π ^ (1 * n))) x) = algebraMap Sb (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb) x := by
      intro x
      show eb.symm (c₁.symm (τ x)) = _
      rw [hτ, RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]
    let ρₐ : (UVCrossingModel W (π ^ (1 * n))) ≃ₐ[Sb] (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb) := AlgEquiv.ofRingEquiv (f := c₁.symm.trans eb.symm) hρcomm
    let Tₐ : TensorProduct Sb (UVCrossingModel W (π ^ (1 * n))) S ≃ₐ[Sb] TensorProduct Sb (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb) S := Algebra.TensorProduct.congr ρₐ AlgEquiv.refl
    have hL : ∀ z, (Algebra.TensorProduct.lift (Algebra.ofId (UVCrossingModel W (π ^ (1 * n))) (AdicCompletion (IsLocalRing.maximalIdeal S) S)) (IsScalarTower.toAlgHom Sb S (AdicCompletion (IsLocalRing.maximalIdeal S) S))
        (fun _ _ => Commute.all _ _) : TensorProduct Sb (UVCrossingModel W (π ^ (1 * n))) S →ₐ[(UVCrossingModel W (π ^ (1 * n)))] (AdicCompletion (IsLocalRing.maximalIdeal S) S)) z = etens (Tₐ z) := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul r s =>
        rw [Algebra.TensorProduct.lift_tmul]
        show ψ r * algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) s = etens (Tₐ (r ⊗ₜ s))
        have hT : Tₐ (r ⊗ₜ[Sb] s) = (ρₐ r) ⊗ₜ[Sb] s := by
          first
            | rfl
            | simp [Tₐ, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
        rw [hT, show (ρₐ r) ⊗ₜ[Sb] s = ((ρₐ r) ⊗ₜ[Sb] (1 : S)) * ((1 : (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb)) ⊗ₜ[Sb] s) by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one (ρₐ r), one_mul s], map_mul, hetens₁, hetens₂, hψ]
        rfl
      | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]
    have hfun : ⇑(Algebra.TensorProduct.lift (Algebra.ofId (UVCrossingModel W (π ^ (1 * n))) (AdicCompletion (IsLocalRing.maximalIdeal S) S)) (IsScalarTower.toAlgHom Sb S (AdicCompletion (IsLocalRing.maximalIdeal S) S))
        (fun _ _ => Commute.all _ _) : TensorProduct Sb (UVCrossingModel W (π ^ (1 * n))) S →ₐ[(UVCrossingModel W (π ^ (1 * n)))] (AdicCompletion (IsLocalRing.maximalIdeal S) S)) = ⇑etens ∘ ⇑Tₐ := funext hL
    rw [hfun]
    exact etens.bijective.comp Tₐ.bijective
  have G36_hB : ∀ (𝔭 : Ideal (AdicCompletion (IsLocalRing.maximalIdeal S) S)) [𝔭.IsPrime], ¬ 𝔭.IsMaximal → Algebra.IsUnramifiedAt (UVCrossingModel W (π ^ (1 * n))) 𝔭 := by
    intro 𝔭 _ h𝔭
    have h𝔔 : ¬ (𝔭.comap (etens : TensorProduct Sb (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb) S →+* (AdicCompletion (IsLocalRing.maximalIdeal S) S))).IsMaximal := by
      intro hmax
      apply h𝔭
      have : 𝔭 = (𝔭.comap (etens : TensorProduct Sb (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb) S →+* (AdicCompletion (IsLocalRing.maximalIdeal S) S))).comap (etens.symm : (AdicCompletion (IsLocalRing.maximalIdeal S) S) →+* TensorProduct Sb (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb) S) := by
        ext x; simp only [Ideal.mem_comap, RingHom.coe_coe, RingEquiv.apply_symm_apply]
      rw [this]
      exact Ideal.comap_isMaximal_of_surjective _ etens.symm.surjective
    have hU : Algebra.IsUnramifiedAt (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb) (𝔭.comap (etens : TensorProduct Sb (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb) S →+* (AdicCompletion (IsLocalRing.maximalIdeal S) S))) := hM5a _ h𝔔

    letI algφ : Algebra (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb) (AdicCompletion (IsLocalRing.maximalIdeal S) S) := φh.toAlgebra
    haveI : IsScalarTower (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb) (AdicCompletion (IsLocalRing.maximalIdeal S) S) (Localization.AtPrime 𝔭) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let f := Localization.localRingHom (𝔭.comap (etens : TensorProduct Sb (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb) S →+* (AdicCompletion (IsLocalRing.maximalIdeal S) S))) 𝔭 (etens : TensorProduct Sb (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb) S →+* (AdicCompletion (IsLocalRing.maximalIdeal S) S)) rfl
    have h𝔭' : 𝔭 = (𝔭.comap (etens : TensorProduct Sb (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb) S →+* (AdicCompletion (IsLocalRing.maximalIdeal S) S))).comap (etens.symm : (AdicCompletion (IsLocalRing.maximalIdeal S) S) →+* TensorProduct Sb (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb) S) := by
      ext x; simp only [Ideal.mem_comap, RingHom.coe_coe, RingEquiv.apply_symm_apply]
    let g := Localization.localRingHom 𝔭 (𝔭.comap (etens : TensorProduct Sb (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb) S →+* (AdicCompletion (IsLocalRing.maximalIdeal S) S))) (etens.symm : (AdicCompletion (IsLocalRing.maximalIdeal S) S) →+* TensorProduct Sb (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb) S) h𝔭'
    have hf : ∀ x, f (algebraMap _ (Localization.AtPrime (𝔭.comap (etens : TensorProduct Sb (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb) S →+* (AdicCompletion (IsLocalRing.maximalIdeal S) S)))) x) = algebraMap (AdicCompletion (IsLocalRing.maximalIdeal S) S) (Localization.AtPrime 𝔭) (etens x) := fun x =>
      Localization.localRingHom_to_map _ _ _ rfl x
    have hg : ∀ y, g (algebraMap (AdicCompletion (IsLocalRing.maximalIdeal S) S) (Localization.AtPrime 𝔭) y) = algebraMap _ (Localization.AtPrime (𝔭.comap (etens : TensorProduct Sb (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb) S →+* (AdicCompletion (IsLocalRing.maximalIdeal S) S)))) (etens.symm y) := fun y =>
      Localization.localRingHom_to_map _ _ _ h𝔭' y
    have hfg : f.comp g = RingHom.id _ := by
      refine IsLocalization.ringHom_ext 𝔭.primeCompl ?_
      ext y
      simp only [RingHom.comp_apply, RingHom.id_apply]
      rw [hg, hf]
      simp
    have hgf : g.comp f = RingHom.id _ := by
      refine IsLocalization.ringHom_ext (𝔭.comap (etens : TensorProduct Sb (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb) S →+* (AdicCompletion (IsLocalRing.maximalIdeal S) S))).primeCompl ?_
      refine RingHom.ext fun x => ?_
      simp only [RingHom.comp_apply, RingHom.id_apply]
      rw [hf, hg]
      simp
    let eL : (Localization.AtPrime (𝔭.comap (etens : TensorProduct Sb (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb) S →+* (AdicCompletion (IsLocalRing.maximalIdeal S) S)))) ≃ₐ[(AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb)] (Localization.AtPrime 𝔭) :=
      AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom f g hfg hgf) (by
        intro x
        show f (algebraMap (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb) _ x) = algebraMap (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb) _ x
        rw [IsScalarTower.algebraMap_apply (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb) (TensorProduct Sb (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb) S) (Localization.AtPrime (𝔭.comap (etens : TensorProduct Sb (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb) S →+* (AdicCompletion (IsLocalRing.maximalIdeal S) S)))), hf,
          IsScalarTower.algebraMap_apply (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb) (AdicCompletion (IsLocalRing.maximalIdeal S) S) (Localization.AtPrime 𝔭)]
        congr 1
        show etens (algebraMap (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb) (TensorProduct Sb (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb) S) x) = φh x
        exact hetens₁ x)
    haveI : Algebra.FormallyUnramified (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb) (Localization.AtPrime (𝔭.comap (etens : TensorProduct Sb (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb) S →+* (AdicCompletion (IsLocalRing.maximalIdeal S) S)))) := hU
    have hA : Algebra.FormallyUnramified (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb) (Localization.AtPrime 𝔭) := Algebra.FormallyUnramified.of_equiv (A := (Localization.AtPrime (𝔭.comap (etens : TensorProduct Sb (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb) S →+* (AdicCompletion (IsLocalRing.maximalIdeal S) S))))) eL

    letI algρ : Algebra (UVCrossingModel W (π ^ (1 * n))) (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb) := ((c₁.symm.trans eb.symm : (UVCrossingModel W (π ^ (1 * n))) ≃+* (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb)) : (UVCrossingModel W (π ^ (1 * n))) →+* (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb)).toAlgebra
    haveI : IsScalarTower (UVCrossingModel W (π ^ (1 * n))) (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb) (Localization.AtPrime 𝔭) := by
      refine IsScalarTower.of_algebraMap_eq (fun r => ?_)
      rw [IsScalarTower.algebraMap_apply (UVCrossingModel W (π ^ (1 * n))) (AdicCompletion (IsLocalRing.maximalIdeal S) S) (Localization.AtPrime 𝔭), IsScalarTower.algebraMap_apply (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb) (AdicCompletion (IsLocalRing.maximalIdeal S) S) (Localization.AtPrime 𝔭)]
      congr 1
      exact hψ r
    haveI : Algebra.FormallyUnramified (UVCrossingModel W (π ^ (1 * n))) (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb) := by
      refine Algebra.FormallyUnramified.of_surjective (Algebra.ofId (UVCrossingModel W (π ^ (1 * n))) (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb)) ?_
      exact (c₁.symm.trans eb.symm).surjective
    haveI := hA
    exact Algebra.FormallyUnramified.comp (UVCrossingModel W (π ^ (1 * n))) (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb) (Localization.AtPrime 𝔭)

  haveI : FaithfulSMul Sb (UVCrossingModel W (π ^ (1 * n))) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hτ_inj
  haveI : Module.Flat Sb (UVCrossingModel W (π ^ (1 * n))) := by
    have hρlin : ∀ (c : Sb) (x : (UVCrossingModel W (π ^ (1 * n)))), (c₁.symm.trans eb.symm) (c • x) = c • (c₁.symm.trans eb.symm) x := by
      intro c x
      rw [Algebra.smul_def, Algebra.smul_def, map_mul]
      congr 1
      show eb.symm (c₁.symm (τ c)) = _
      rw [hτ, RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]
    let ρₗ : (UVCrossingModel W (π ^ (1 * n))) ≃ₗ[Sb] (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb) := { (c₁.symm.trans eb.symm).toAddEquiv with map_smul' := hρlin }
    exact Module.Flat.of_linearEquiv ρₗ

  have hSbK0_inj : Function.Injective ((algebraMap (UVCrossingModel W (π ^ (1 * n))) (FractionRing (UVCrossingModel W (π ^ (1 * n))))).comp τ) :=
    (IsFractionRing.injective (UVCrossingModel W (π ^ (1 * n))) (FractionRing (UVCrossingModel W (π ^ (1 * n))))).comp hτ_inj
  letI algK₁K0 : Algebra K₁ (FractionRing (UVCrossingModel W (π ^ (1 * n)))) := (IsFractionRing.lift (K := K₁) hSbK0_inj).toAlgebra

  haveI : IsScalarTower Sb (UVCrossingModel W (π ^ (1 * n))) (FractionRing (UVCrossingModel W (π ^ (1 * n)))) := inferInstance
  haveI : IsScalarTower Sb K₁ (FractionRing (UVCrossingModel W (π ^ (1 * n)))) := IsScalarTower.of_algebraMap_eq (fun x => by
    rw [IsScalarTower.algebraMap_apply Sb (UVCrossingModel W (π ^ (1 * n))) (FractionRing (UVCrossingModel W (π ^ (1 * n))))]
    exact (IsFractionRing.lift_algebraMap hSbK0_inj x).symm)

  have G35_hdimR : ringKrullDim (UVCrossingModel W (π ^ (1 * n))) ≤ (2 : WithBot ℕ∞) := UVCrossingModel.ringKrullDim_le_two π hπ (1 * n) h1n
  have G27_hR : ∀ (𝔯 : Ideal (UVCrossingModel W (π ^ (1 * n)))) [𝔯.IsPrime], 𝔯 ≠ IsLocalRing.maximalIdeal (UVCrossingModel W (π ^ (1 * n))) → IsRegularLocalRing (Localization.AtPrime 𝔯) := by
    intro 𝔯 _ h𝔯
    exact IsIntegrallyClosed.isRegularLocalRing_localization_of_ne_maximalIdeal_of_ringKrullDim_le_two G35_hdimR 𝔯 h𝔯
  obtain ⟨⟨e0, he0⟩, G32_hinj⟩ :=
    IsLocalization.exists_algEquiv_tensorProduct_and_injective_of_bijective_baseChange
      (R := Sb) (S := S) (Rhat := (UVCrossingModel W (π ^ (1 * n)))) (T := (AdicCompletion (IsLocalRing.maximalIdeal S) S)) (K₁ := K₁) (K := K) (E := (FractionRing (UVCrossingModel W (π ^ (1 * n))))) G39'_hT (Localization (Algebra.algebraMapSubmonoid (AdicCompletion (IsLocalRing.maximalIdeal S) S) (nonZeroDivisors (UVCrossingModel W (π ^ (1 * n))))))
  haveI : Algebra.IsSeparable K₁ K := inferInstance
  obtain ⟨hred, hsepT, -⟩ := Algebra.IsSeparable.isReduced_and_isSeparable_and_finite_tensorProduct K₁ K (FractionRing (UVCrossingModel W (π ^ (1 * n))))
  haveI : IsReduced (Localization (Algebra.algebraMapSubmonoid (AdicCompletion (IsLocalRing.maximalIdeal S) S) (nonZeroDivisors (UVCrossingModel W (π ^ (1 * n)))))) := by
    haveI := hred
    exact isReduced_of_injective e0.symm e0.symm.injective
  haveI : Algebra.IsSeparable (FractionRing (UVCrossingModel W (π ^ (1 * n)))) (Localization (Algebra.algebraMapSubmonoid (AdicCompletion (IsLocalRing.maximalIdeal S) S) (nonZeroDivisors (UVCrossingModel W (π ^ (1 * n)))))) := by
    haveI := hsepT
    exact Algebra.IsSeparable.of_equiv_equiv (RingEquiv.refl (FractionRing (UVCrossingModel W (π ^ (1 * n))))) e0.toRingEquiv
      (RingHom.ext fun x => (e0.commutes x).symm)
  have hR1 := Algebra.IsUnramifiedAt.isRegularLocalRing_localization_of_ne_maximalIdeal (R₀ := (UVCrossingModel W (π ^ (1 * n)))) G27_hR G35_hdimR (FractionRing (UVCrossingModel W (π ^ (1 * n)))) (B := (AdicCompletion (IsLocalRing.maximalIdeal S) S)) (Localization (Algebra.algebraMapSubmonoid (AdicCompletion (IsLocalRing.maximalIdeal S) S) (nonZeroDivisors (UVCrossingModel W (π ^ (1 * n)))))) G32_hinj G36_hB
  have G31_hdim : ringKrullDim (AdicCompletion (IsLocalRing.maximalIdeal S) S) ≤ (2 : WithBot ℕ∞) := by rw [IsLocalRing.ringKrullDim_adicCompletion_maximalIdeal_eq]; exact hdimS
  obtain ⟨b, hb, hreg⟩ := IsIntegrallyClosed.exists_isRegular_pair_of_two_le_ringKrullDim hdimS' t ht ht0
  have hw := hreg.toIsWeaklyRegular.of_flat (S := (AdicCompletion (IsLocalRing.maximalIdeal S) S))
  simp only [List.map_cons, List.map_nil] at hw
  have hloc : ∀ s : S, s ∈ IsLocalRing.maximalIdeal S → algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) s ∈ IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal S) S) := by
    intro s hs
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact Ideal.mem_map_of_mem _ hs
  have hab : RingTheory.Sequence.IsRegular (AdicCompletion (IsLocalRing.maximalIdeal S) S) [algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) t, algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) b] := by
    refine ⟨hw, ?_⟩
    intro htop
    have hle : Ideal.ofList [algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) t, algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) b] ≤ IsLocalRing.maximalIdeal _ := by
      rw [Ideal.ofList, Ideal.span_le]
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq] at hr
      rcases hr with rfl | rfl
      · exact hloc _ ht
      · exact hloc _ hb
    rw [Ideal.smul_eq_mul, Ideal.mul_top] at htop
    have h1 : (1 : (AdicCompletion (IsLocalRing.maximalIdeal S) S)) ∈ Ideal.ofList [algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) t, algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) b] := by
      rw [← htop]; exact Submodule.mem_top
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (Ideal.eq_top_of_isUnit_mem _ (hle h1) isUnit_one)
  obtain ⟨hŜdom, hŜicl, -, hF0frac⟩ :=
    IsLocalRing.isDomain_and_isIntegrallyClosed_and_isFractionRing_of_forall_not_isMaximal_isRegularLocalRing
      (R₀ := (UVCrossingModel W (π ^ (1 * n)))) (FractionRing (UVCrossingModel W (π ^ (1 * n)))) (B := (AdicCompletion (IsLocalRing.maximalIdeal S) S)) G31_hdim (Localization (Algebra.algebraMapSubmonoid (AdicCompletion (IsLocalRing.maximalIdeal S) S) (nonZeroDivisors (UVCrossingModel W (π ^ (1 * n)))))) G32_hinj hR1 _ _ hab
  haveI : IsDomain (AdicCompletion (IsLocalRing.maximalIdeal S) S) := hŜdom
  haveI : IsIntegrallyClosed (AdicCompletion (IsLocalRing.maximalIdeal S) S) := hŜicl

  letI : Algebra (FractionRing (UVCrossingModel W (π ^ (1 * n)))) (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal S) S)) := FractionRing.liftAlgebra (UVCrossingModel W (π ^ (1 * n))) (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal S) S))
  haveI : IsScalarTower (UVCrossingModel W (π ^ (1 * n))) (FractionRing (UVCrossingModel W (π ^ (1 * n)))) (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal S) S)) := FractionRing.isScalarTower_liftAlgebra _ _

  have hSF_inj : Function.Injective ((algebraMap (AdicCompletion (IsLocalRing.maximalIdeal S) S) (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal S) S))).comp (algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S))) :=
    (IsFractionRing.injective (AdicCompletion (IsLocalRing.maximalIdeal S) S) (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal S) S))).comp (AdicCompletion.of_injective (I := IsLocalRing.maximalIdeal S) (M := S))
  letI algKF : Algebra K (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal S) S)) := (IsFractionRing.lift (K := K) hSF_inj).toAlgebra

  haveI : IsScalarTower S (AdicCompletion (IsLocalRing.maximalIdeal S) S) (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal S) S)) := inferInstance
  haveI : IsScalarTower S K (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal S) S)) := IsScalarTower.of_algebraMap_eq (fun x => by
    rw [IsScalarTower.algebraMap_apply S (AdicCompletion (IsLocalRing.maximalIdeal S) S) (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal S) S))]
    exact (IsFractionRing.lift_algebraMap hSF_inj x).symm)

  letI algK₁F : Algebra K₁ (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal S) S)) := ((algebraMap (FractionRing (UVCrossingModel W (π ^ (1 * n)))) (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal S) S))).comp (algebraMap K₁ (FractionRing (UVCrossingModel W (π ^ (1 * n)))))).toAlgebra
  haveI : IsScalarTower K₁ (FractionRing (UVCrossingModel W (π ^ (1 * n)))) (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal S) S)) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower K₁ K (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal S) S)) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    refine IsLocalization.ringHom_ext (nonZeroDivisors Sb) ?_
    ext x
    simp only [RingHom.comp_apply]
    rw [IsScalarTower.algebraMap_apply K₁ (FractionRing (UVCrossingModel W (π ^ (1 * n)))) (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal S) S)), ← IsScalarTower.algebraMap_apply Sb K₁ (FractionRing (UVCrossingModel W (π ^ (1 * n)))),
      IsScalarTower.algebraMap_apply Sb (UVCrossingModel W (π ^ (1 * n))) (FractionRing (UVCrossingModel W (π ^ (1 * n)))), ← IsScalarTower.algebraMap_apply (UVCrossingModel W (π ^ (1 * n))) (FractionRing (UVCrossingModel W (π ^ (1 * n)))) (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal S) S)),
      IsScalarTower.algebraMap_apply (UVCrossingModel W (π ^ (1 * n))) (AdicCompletion (IsLocalRing.maximalIdeal S) S) (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal S) S))]
    rw [show algebraMap (UVCrossingModel W (π ^ (1 * n))) (AdicCompletion (IsLocalRing.maximalIdeal S) S) (algebraMap Sb (UVCrossingModel W (π ^ (1 * n))) x) = algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) (algebraMap Sb S x) from hψτ x]
    rw [← IsScalarTower.algebraMap_apply Sb K₁ K, IsScalarTower.algebraMap_apply Sb S K,
      ← IsScalarTower.algebraMap_apply S K (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal S) S)), IsScalarTower.algebraMap_apply S (AdicCompletion (IsLocalRing.maximalIdeal S) S) (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal S) S))]

  haveI : IsScalarTower Sb S K := inferInstance
  haveI : IsScalarTower (UVCrossingModel W (π ^ (1 * n))) (AdicCompletion (IsLocalRing.maximalIdeal S) S) (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal S) S)) := inferInstance
  have G39_bij := IsFractionRing.bijective_tensorProduct_lift_of_bijective_baseChange
    (R := Sb) (S := S) (Rhat := (UVCrossingModel W (π ^ (1 * n)))) (T := (AdicCompletion (IsLocalRing.maximalIdeal S) S)) (K₁ := K₁) (K := K) (E := (FractionRing (UVCrossingModel W (π ^ (1 * n))))) (F := (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal S) S))) G39'_hT
  obtain ⟨hfdF, hgalF, ⟨egal⟩, hrankF⟩ :=
    IsGalois.of_bijective_tensorProduct_lift (K₁ := K₁) (K := K) (E := (FractionRing (UVCrossingModel W (π ^ (1 * n))))) (F := (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal S) S))) G39_bij
  haveI : FiniteDimensional (FractionRing (UVCrossingModel W (π ^ (1 * n)))) (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal S) S)) := hfdF
  haveI : IsGalois (FractionRing (UVCrossingModel W (π ^ (1 * n)))) (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal S) S)) := hgalF
  have hcyc : IsCyclic ((FractionRing (AdicCompletion (IsLocalRing.maximalIdeal S) S)) ≃ₐ[(FractionRing (UVCrossingModel W (π ^ (1 * n))))] (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal S) S))) := isCyclic_of_surjective egal.symm.toMonoidHom egal.symm.surjective
  have hdeg : Module.finrank (FractionRing (UVCrossingModel W (π ^ (1 * n)))) (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal S) S)) = n := by rw [hrankF, hdegK]

  have G24_hres : ∀ b : (AdicCompletion (IsLocalRing.maximalIdeal S) S), ∃ w : W,
      b - algebraMap (UVCrossingModel W (π ^ (1 * n))) (AdicCompletion (IsLocalRing.maximalIdeal S) S) (const (π ^ (1 * n)) w) ∈ IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal S) S) := by
    intro b

    obtain ⟨s, hs⟩ : ∃ s : S, b - algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) s ∈ IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal S) S) := by
      obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal S) 1 b)
      refine ⟨s, ?_⟩
      rw [← pow_one (IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal S) S)), AdicCompletion.maximalIdeal_pow_eq_ker_evalₐ 1, RingHom.mem_ker,
        map_sub, sub_eq_zero, ← hs]
      rfl

    obtain ⟨r, hr⟩ := hresS s

    obtain ⟨w, hw⟩ : ∃ w : W, τ r - const (π ^ (1 * n)) w ∈ IsLocalRing.maximalIdeal (UVCrossingModel W (π ^ (1 * n))) := by
      have hπu : ¬IsUnit (π ^ (1 * n)) := by
        rw [isUnit_pow_iff (by omega : 1 * n ≠ 0)]
        exact hπ.not_isUnit
      exact ModularCurve.UVCrossingModel.exists_sub_const_mem_maximalIdeal hπu (τ r)
    refine ⟨w, ?_⟩
    have hψloc : ∀ x : (UVCrossingModel W (π ^ (1 * n))), x ∈ IsLocalRing.maximalIdeal (UVCrossingModel W (π ^ (1 * n))) → algebraMap (UVCrossingModel W (π ^ (1 * n))) (AdicCompletion (IsLocalRing.maximalIdeal S) S) x ∈ IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal S) S) := by
      intro x hx
      haveI : Algebra.IsIntegral (UVCrossingModel W (π ^ (1 * n))) (AdicCompletion (IsLocalRing.maximalIdeal S) S) := Algebra.IsIntegral.of_finite _ _
      have hcm : (IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal S) S)).comap (algebraMap (UVCrossingModel W (π ^ (1 * n))) (AdicCompletion (IsLocalRing.maximalIdeal S) S)) = IsLocalRing.maximalIdeal (UVCrossingModel W (π ^ (1 * n))) :=
        IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _)
      rw [← hcm] at hx
      exact hx
    have e1 : b - algebraMap (UVCrossingModel W (π ^ (1 * n))) (AdicCompletion (IsLocalRing.maximalIdeal S) S) (const (π ^ (1 * n)) w) =
        (b - algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) s) + algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) (s - algebraMap Sb S r) +
          algebraMap (UVCrossingModel W (π ^ (1 * n))) (AdicCompletion (IsLocalRing.maximalIdeal S) S) (τ r - const (π ^ (1 * n)) w) := by
      rw [map_sub, map_sub, show algebraMap (UVCrossingModel W (π ^ (1 * n))) (AdicCompletion (IsLocalRing.maximalIdeal S) S) (τ r) = algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) (algebraMap Sb S r) from hψτ r]
      ring
    rw [e1]
    exact add_mem (add_mem hs (hloc _ hr)) (hψloc _ hw)
  have hunr_ht : ∀ (𝔭 : Ideal (AdicCompletion (IsLocalRing.maximalIdeal S) S)) [𝔭.IsPrime],
      (𝔭.comap (algebraMap (UVCrossingModel W (π ^ (1 * n))) (AdicCompletion (IsLocalRing.maximalIdeal S) S))).height = 1 → Algebra.IsUnramifiedAt (UVCrossingModel W (π ^ (1 * n))) 𝔭 := by
    intro 𝔭 _ h
    refine G36_hB 𝔭 ?_
    intro hmax
    haveI : Algebra.IsIntegral (UVCrossingModel W (π ^ (1 * n))) (AdicCompletion (IsLocalRing.maximalIdeal S) S) := Algebra.IsIntegral.of_finite _ _
    have h1 : 𝔭.comap (algebraMap (UVCrossingModel W (π ^ (1 * n))) (AdicCompletion (IsLocalRing.maximalIdeal S) S)) = IsLocalRing.maximalIdeal (UVCrossingModel W (π ^ (1 * n))) :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal 𝔭)
    have h2 : ringKrullDim (UVCrossingModel W (π ^ (1 * n))) = ringKrullDim Sb := by
      rw [ringKrullDim_eq_of_ringEquiv (c₁.symm.trans eb.symm), IsLocalRing.ringKrullDim_adicCompletion_maximalIdeal_eq]
    have h3 : (ringKrullDim (UVCrossingModel W (π ^ (1 * n))) : WithBot ℕ∞) = 1 := by
      rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ← h1, h]; rfl
    have h4 := hdimSb
    rw [← h2, h3] at h4
    exact absurd h4 (by decide)
  obtain ⟨e, he⟩ := ModularCurve.UVCrossingModel.exists_ringEquiv_uvCrossingModel_of_isGalois_of_isCyclic_of_isUnramifiedAt_of_residue π hπ n hn hnW hμ (AdicCompletion (IsLocalRing.maximalIdeal S) S) (FractionRing (UVCrossingModel W (π ^ (1 * n)))) (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal S) S)) hcyc hdeg hunr_ht G24_hres
  refine ⟨e, fun x w hx => ?_⟩
  have hx' : eb.symm (const (π ^ n) w) = algebraMap Sb (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb) x := by
    rw [RingEquiv.symm_apply_eq]; exact hx.symm
  have h1 : c₁.symm (const (π ^ (1 * n)) w) = const (π ^ n) w := by
    rw [RingEquiv.symm_apply_eq]; exact (hc₁ (MvPowerSeries.C w)).symm
  have key : algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) (algebraMap Sb S x) = algebraMap (UVCrossingModel W (π ^ (1 * n))) (AdicCompletion (IsLocalRing.maximalIdeal S) S) (const (π ^ (1 * n)) w) := by
    symm
    show ψ _ = _
    rw [hψ, h1, hx', hφh_comm]
  rw [key, he w]

end

end S_ModularCurve_UVCrossingModel_exists_ringEquiv_adicCompletion_uvCrossingModel_of_moduleFinite_of_isUnramifiedAt_of_isGalois
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_exists_ringEquiv_adicCompletion_uvCrossingModel_of_moduleFinite_of_isUnramifiedAt_of_isGalois (solution)
