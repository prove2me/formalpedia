-- Prove2me | solution 1 for MazurTransfer.Order13GoodPrimeActualNormInertia.actual_norm_inertia_fixed_of_image_fixed
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T06:21:00.520717+00:00
-- url     : https://prove2.me/submissions/feb1e05a-31d9-423a-959b-b4527ff2053e

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: inertia fixes every geometric norm lift of a rational
point for the SAME actual rational Picard norm maps at good primes.
Named downstream consumer: unramified local Kummer restrictions.
-/
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_MazurTransfer_Order13GoodPrimeIntegralNormExtensionsData
import Theorems.Thm_MazurTransfer_Order13LocalRingInValuationSubring_local_coefficients_mem
import Theorems.Thm_MazurTransfer_ProperGenericInertiaFibres_generic_inertia_fixed_of_image_fixed
import Theorems.Thm_MazurTransfer_Order13GoodPrimeIntegralNormFinite_integral_norms_finite
import Theorems.Thm_MazurTransfer_Order13GoodPrimeIntegralNormFinite_integral_norms_formallyUnramified
noncomputable section
open MazurTransfer
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open Order13GoodPrimeLocalPicardModels Order13LocalIntegralCoefficientMaps
open Order13GoodPrimeLocalGenericPicardComparison Order13GoodPrimeIntegralNormExtensions
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardSchemeNineteenNorm

theorem solution (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (hne : q ≠ 19)
    {Ω : Type} [Field Ω] [Algebra ℚ Ω] [Algebra (LocalRing q) Ω]
    [IsScalarTower (LocalRing q) ℚ Ω]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase)
    (hφ : φ = schemePi ∨ φ = schemePiConjugate)
    (A : ValuationSubring Ω) (hA : A.LiesOverPrime q)
    (σ : Ω ≃ₐ[ℚ] Ω) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℚ Ω))) actualPicard.toBase)
    (hx : Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.val ≫ φ.left =
      x.val ≫ φ.left) :
    Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.val = x.val := by
  let e := actualLocalGenericOverIso q hq
  let xg : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℚ Ω)))
      (pullback.snd (localPicard q hq).toBase (specGenericFibreInclusion (LocalRing q) ℚ)) :=
    ⟨x.val ≫ e.hom.left, by erw [Category.assoc, e.hom.w, x.property]⟩
  let ψ := integralNorm q hq φ
  have hu : FormallyUnramified ψ.val := by
    rcases hφ with rfl | rfl
    · exact (MazurTransfer.Order13GoodPrimeIntegralNormFinite.integral_norms_formallyUnramified q hq hne).1
    · exact (MazurTransfer.Order13GoodPrimeIntegralNormFinite.integral_norms_formallyUnramified q hq hne).2
  have hf : IsFinite ψ.val := by
    rcases hφ with rfl | rfl
    · exact (MazurTransfer.Order13GoodPrimeIntegralNormFinite.integral_norms_finite q hq hne).1
    · exact (MazurTransfer.Order13GoodPrimeIntegralNormFinite.integral_norms_finite q hq hne).2
  letI : FormallyUnramified ψ.val := hu
  letI : IsFinite ψ.val := hf
  letI : IsProper (localPicard q hq).toBase := (localPicard_geometry q hq).2.1
  have hxg : Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ xg.val ≫
      (genericFibreRestrict (LocalRing q) ℚ (localPicard q hq).toBase
        (localPicard q hq).toBase ψ).val =
      xg.val ≫ (genericFibreRestrict (LocalRing q) ℚ (localPicard q hq).toBase
        (localPicard q hq).toBase ψ).val := by
    rw [integralNorm_restrict]
    change Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫
      (x.val ≫ e.hom.left) ≫ (localGenericNorm q hq φ).val =
      (x.val ≫ e.hom.left) ≫ (localGenericNorm q hq φ).val
    erw [Category.assoc, localGenericNorm_intertwine q hq φ]
    have h := congrArg (fun z => z ≫ e.hom.left) hx
    erw [Category.assoc] at h
    exact h
  have hg := ProperGenericInertiaFibres.generic_inertia_fixed_of_image_fixed ℚ
    (localPicard q hq).toBase ψ A
    (fun r => Order13LocalRingInValuationSubring.local_coefficients_mem q A hA r)
    σ hσ xg hxg
  have hei : e.hom.left ≫ e.inv.left = 𝟙 _ :=
    congrArg (fun z => z.left) e.hom_inv_id
  have h := congrArg (fun z => z ≫ e.inv.left) hg
  change (Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫
    (x.val ≫ e.hom.left)) ≫ e.inv.left = (x.val ≫ e.hom.left) ≫ e.inv.left at h
  erw [Category.assoc, Category.assoc, hei, Category.comp_id] at h
  exact h

#print axioms solution
