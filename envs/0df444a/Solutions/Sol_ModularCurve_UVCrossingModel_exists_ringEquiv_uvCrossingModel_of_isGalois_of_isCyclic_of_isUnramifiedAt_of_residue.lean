-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.exists_ringEquiv_uvCrossingModel_of_isGalois_of_isCyclic_of_isUnramifiedAt_of_residue
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/ab8c3235-dd87-5296-a3c4-26262445e573

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_ringEquiv_integralClosure_uvCrossingModel_pow_of_pow_eq_unit_mul_U
import Theorems.Thm_ModularCurve_UVCrossingModel_isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_pow_eq_unit_mul_U_of_isCyclic_of_isUnramifiedAt_of_residue_thicknessOne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_exists_ringEquiv_uvCrossingModel_of_isGalois_of_isCyclic_of_isUnramifiedAt_of_residue

set_option autoImplicit false

section
open ModularCurve ModularCurve.UVCrossingModel

theorem solution
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (n : ℕ) (hn : 0 < n) (hnW : IsUnit (n : W))
    (hμ : ∃ ζ : W, IsPrimitiveRoot ζ n)
    (B : Type*) [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [IsLocalRing B] [IsNoetherianRing B]
    [Algebra (UVCrossingModel W (π ^ (1 * n))) B] [Module.Finite (UVCrossingModel W (π ^ (1 * n))) B] [FaithfulSMul (UVCrossingModel W (π ^ (1 * n))) B]
    (K₀ : Type*) [Field K₀] [Algebra (UVCrossingModel W (π ^ (1 * n))) K₀] [IsFractionRing (UVCrossingModel W (π ^ (1 * n))) K₀]
    (F : Type*) [Field F] [Algebra K₀ F] [Algebra (UVCrossingModel W (π ^ (1 * n))) F] [IsScalarTower (UVCrossingModel W (π ^ (1 * n))) K₀ F]
    [Algebra B F] [IsScalarTower (UVCrossingModel W (π ^ (1 * n))) B F] [IsFractionRing B F]
    [FiniteDimensional K₀ F] [IsGalois K₀ F] (hcyc : IsCyclic (F ≃ₐ[K₀] F)) (hdeg : Module.finrank K₀ F = n)
    (hunr : ∀ (𝔭 : Ideal B) [𝔭.IsPrime],
      (𝔭.comap (algebraMap (UVCrossingModel W (π ^ (1 * n))) B)).height = 1 →
        Algebra.IsUnramifiedAt (UVCrossingModel W (π ^ (1 * n))) 𝔭)
    (hres : ∀ b : B, ∃ w : W, b - algebraMap (UVCrossingModel W (π ^ (1 * n))) B (const (π ^ (1 * n)) w) ∈ IsLocalRing.maximalIdeal B) :
    ∃ e : B ≃+* UVCrossingModel W π,
      ∀ w : W, e (algebraMap (UVCrossingModel W (π ^ (1 * n))) B (const (π ^ (1 * n)) w)) = const π w := by
  classical
  have h1n : 1 ≤ 1 * n := by rw [Nat.one_mul]; exact hn
  haveI : IsLocalRing (UVCrossingModel W (π ^ (1 * n))) := (isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete π hπ (1 * n) h1n).2.1
  haveI : IsDomain (UVCrossingModel W (π ^ (1 * n))) := (isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete π hπ (1 * n) h1n).1

  haveI : Algebra.IsIntegral (UVCrossingModel W (π ^ (1 * n))) B := Algebra.IsIntegral.of_finite _ _
  have hrange : (IsScalarTower.toAlgHom (UVCrossingModel W (π ^ (1 * n))) B F).range = integralClosure (UVCrossingModel W (π ^ (1 * n))) F := by
    ext x
    constructor
    · rintro ⟨b, rfl⟩
      exact (Algebra.IsIntegral.isIntegral (R := (UVCrossingModel W (π ^ (1 * n)))) b).algebraMap
    · intro hx
      have hx' : IsIntegral B x := (show IsIntegral _ x from hx).tower_top
      obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := B) (K := F)).mp hx'
      exact ⟨y, hy⟩
  have hinjBF : Function.Injective (IsScalarTower.toAlgHom (UVCrossingModel W (π ^ (1 * n))) B F) := IsFractionRing.injective B F
  obtain ⟨ιₐ, hιₐ⟩ : ∃ ιₐ : B ≃ₐ[(UVCrossingModel W (π ^ (1 * n)))] ↥(integralClosure (UVCrossingModel W (π ^ (1 * n))) F), ∀ s : B, ((ιₐ s : ↥(integralClosure (UVCrossingModel W (π ^ (1 * n))) F)) : F) = algebraMap B F s :=
    ⟨(AlgEquiv.ofInjective _ hinjBF).trans (Subalgebra.equivOfEq _ _ hrange), fun s => rfl⟩
  haveI : IsLocalRing ↥(integralClosure (UVCrossingModel W (π ^ (1 * n))) F) := ιₐ.toRingEquiv.isLocalRing

  have hres' : ∀ b : ↥(integralClosure (UVCrossingModel W (π ^ (1 * n))) F), ∃ w : W,
      b - algebraMap (UVCrossingModel W (π ^ (1 * n))) _ (const (π ^ (1 * n)) w) ∈ IsLocalRing.maximalIdeal ↥(integralClosure (UVCrossingModel W (π ^ (1 * n))) F) := by
    intro b'
    obtain ⟨b, rfl⟩ := ιₐ.surjective b'
    obtain ⟨w, hw⟩ := hres b
    refine ⟨w, ?_⟩
    have hmap : ιₐ b - algebraMap (UVCrossingModel W (π ^ (1 * n))) _ (const (π ^ (1 * n)) w) = ιₐ (b - algebraMap (UVCrossingModel W (π ^ (1 * n))) B (const (π ^ (1 * n)) w)) := by
      rw [map_sub, AlgEquiv.commutes]
    rw [hmap]
    haveI : IsLocalHom (ιₐ : B →+* ↥(integralClosure (UVCrossingModel W (π ^ (1 * n))) F)) :=
      ⟨fun a ha => by simpa using ha.map (ιₐ.symm : ↥(integralClosure (UVCrossingModel W (π ^ (1 * n))) F) →+* B)⟩
    exact (map_mem_nonunits_iff (ιₐ : B →+* ↥(integralClosure (UVCrossingModel W (π ^ (1 * n))) F)) _).mpr hw

  have hunr' : ∀ (Q : Ideal ↥(integralClosure (UVCrossingModel W (π ^ (1 * n))) F)) [Q.IsPrime],
      (Q.comap (algebraMap (UVCrossingModel W (π ^ (1 * n))) ↥(integralClosure (UVCrossingModel W (π ^ (1 * n))) F))).height = 1 → Algebra.IsUnramifiedAt (UVCrossingModel W (π ^ (1 * n))) Q := by
    intro Q _ hQ

    have hιalg : (algebraMap (UVCrossingModel W (π ^ (1 * n))) ↥(integralClosure (UVCrossingModel W (π ^ (1 * n))) F)) = (ιₐ : B →+* ↥(integralClosure (UVCrossingModel W (π ^ (1 * n))) F)).comp (algebraMap (UVCrossingModel W (π ^ (1 * n))) B) := by
      exact RingHom.ext fun r => (ιₐ.commutes r).symm
    have h𝔭 : (Q.comap (ιₐ : B →+* ↥(integralClosure (UVCrossingModel W (π ^ (1 * n))) F))).comap (algebraMap (UVCrossingModel W (π ^ (1 * n))) B) =
        Q.comap (algebraMap (UVCrossingModel W (π ^ (1 * n))) ↥(integralClosure (UVCrossingModel W (π ^ (1 * n))) F)) := by
      rw [hιalg, ← Ideal.comap_comap]
    haveI : (Q.comap (ιₐ : B →+* ↥(integralClosure (UVCrossingModel W (π ^ (1 * n))) F))).IsPrime := Ideal.comap_isPrime _ Q
    have hU : Algebra.IsUnramifiedAt (UVCrossingModel W (π ^ (1 * n))) (Q.comap (ιₐ : B →+* ↥(integralClosure (UVCrossingModel W (π ^ (1 * n))) F))) := hunr _ (by rw [h𝔭]; exact hQ)

    have hIJ : Q.comap (ιₐ : B →+* ↥(integralClosure (UVCrossingModel W (π ^ (1 * n))) F)) = Q.comap (ιₐ : B →+* ↥(integralClosure (UVCrossingModel W (π ^ (1 * n))) F)) := rfl
    let f := Localization.localRingHom (Q.comap (ιₐ : B →+* ↥(integralClosure (UVCrossingModel W (π ^ (1 * n))) F))) Q (ιₐ : B →+* ↥(integralClosure (UVCrossingModel W (π ^ (1 * n))) F)) rfl
    have hQ' : Q = (Q.comap (ιₐ : B →+* ↥(integralClosure (UVCrossingModel W (π ^ (1 * n))) F))).comap (ιₐ.symm : ↥(integralClosure (UVCrossingModel W (π ^ (1 * n))) F) →+* B) := by
      ext x; simp [Ideal.mem_comap]
    let g := Localization.localRingHom Q (Q.comap (ιₐ : B →+* ↥(integralClosure (UVCrossingModel W (π ^ (1 * n))) F))) (ιₐ.symm : ↥(integralClosure (UVCrossingModel W (π ^ (1 * n))) F) →+* B) hQ'
    have hf : ∀ x : B, f (algebraMap B _ x) = algebraMap _ _ (ιₐ x) := fun x =>
      Localization.localRingHom_to_map _ _ _ rfl x
    have hg : ∀ y : ↥(integralClosure (UVCrossingModel W (π ^ (1 * n))) F), g (algebraMap _ _ y) = algebraMap B _ (ιₐ.symm y) := fun y =>
      Localization.localRingHom_to_map _ _ _ hQ' y
    have hfg : f.comp g = RingHom.id _ := by
      refine IsLocalization.ringHom_ext Q.primeCompl ?_
      ext y
      simp only [RingHom.comp_apply, RingHom.id_apply]
      rw [hg, hf]
      simp
    have hgf : g.comp f = RingHom.id _ := by
      refine IsLocalization.ringHom_ext (Q.comap (ιₐ : B →+* ↥(integralClosure (UVCrossingModel W (π ^ (1 * n))) F))).primeCompl ?_
      ext x
      simp only [RingHom.comp_apply, RingHom.id_apply]
      rw [hf, hg]
      simp
    let eL : Localization.AtPrime (Q.comap (ιₐ : B →+* ↥(integralClosure (UVCrossingModel W (π ^ (1 * n))) F))) ≃ₐ[(UVCrossingModel W (π ^ (1 * n)))] Localization.AtPrime Q :=
      AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom f g hfg hgf) (by
        intro r
        show f (algebraMap (UVCrossingModel W (π ^ (1 * n))) _ r) = algebraMap (UVCrossingModel W (π ^ (1 * n))) _ r
        rw [IsScalarTower.algebraMap_apply (UVCrossingModel W (π ^ (1 * n))) B (Localization.AtPrime (Q.comap (ιₐ : B →+* ↥(integralClosure (UVCrossingModel W (π ^ (1 * n))) F)))),
          Localization.localRingHom_to_map, IsScalarTower.algebraMap_apply (UVCrossingModel W (π ^ (1 * n))) ↥(integralClosure (UVCrossingModel W (π ^ (1 * n))) F) (Localization.AtPrime Q)]
        congr 1
        exact ιₐ.commutes r)
    exact Algebra.FormallyUnramified.of_equiv eL
  obtain ⟨u, θ, hθ, hFθ⟩ :=
    ModularCurve.UVCrossingModel.exists_pow_eq_unit_mul_U_of_isCyclic_of_isUnramifiedAt_of_residue_thicknessOne π hπ n hn hnW hμ
      K₀ F hcyc hdeg hunr' hres'
  obtain ⟨-, -, e₈, he₈, -, -, -⟩ :=
    ModularCurve.UVCrossingModel.exists_ringEquiv_integralClosure_uvCrossingModel_pow_of_pow_eq_unit_mul_U π hπ 1 n Nat.one_pos hn hnW u
      K₀ F θ hθ hFθ
  have hcast₂ : uvCrossingIdeal W (π ^ 1) = uvCrossingIdeal W π := by rw [pow_one]
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : UVCrossingModel W (π ^ 1) ≃+* UVCrossingModel W π, ∀ w : W, c₂ (const (π ^ 1) w) = const π w :=
    ⟨Ideal.quotEquivOfEq hcast₂, fun w => rfl⟩
  refine ⟨(ιₐ.toRingEquiv.trans e₈).trans c₂, fun w => ?_⟩
  simp only [RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]
  rw [he₈ w, hc₂]

end

end S_ModularCurve_UVCrossingModel_exists_ringEquiv_uvCrossingModel_of_isGalois_of_isCyclic_of_isUnramifiedAt_of_residue
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_exists_ringEquiv_uvCrossingModel_of_isGalois_of_isCyclic_of_isUnramifiedAt_of_residue (solution)
