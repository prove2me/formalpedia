-- Prove2me | solution 1 for MazurTransfer.Order13GoodPrimeActualNormInertia.actual_norm_lift_of_rational_point_inertia_fixed
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T06:28:22.400167+00:00
-- url     : https://prove2.me/submissions/1dd15120-4aa6-4cea-9527-c5a55e1f5ea0

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: inertia fixes every geometric norm lift of a rational
point for the SAME actual rational Picard norm maps at good primes.
Named downstream consumer: unramified local Kummer restrictions.
-/
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_MazurTransfer_Order13GoodPrimeIntegralNormExtensionsData
import Theorems.Thm_MazurTransfer_Order13GoodPrimeActualNormInertia_actual_norm_inertia_fixed_of_image_fixed
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
    (p : Spec (CommRingCat.of ℚ) ⟶ actualPicard.P)
    (hx : x.val ≫ φ.left = Spec.map (CommRingCat.ofHom (algebraMap ℚ Ω)) ≫ p) :
    Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.val = x.val := by
  apply MazurTransfer.Order13GoodPrimeActualNormInertia.actual_norm_inertia_fixed_of_image_fixed q hq hne φ hφ A hA σ hσ x
  rw [hx, ← Category.assoc]
  have hb : Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℚ Ω)) =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ Ω)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    apply congrArg Spec.map
    apply congrArg CommRingCat.ofHom
    exact RingHom.ext (fun r => σ.commutes r)
  rw [hb]

#print axioms solution
