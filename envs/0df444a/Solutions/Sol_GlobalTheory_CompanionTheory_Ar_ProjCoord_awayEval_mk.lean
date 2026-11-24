-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.ProjCoord.awayEval_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:09:38.970662+00:00
-- url     : https://prove2.me/submissions/8fa93af2-7cf1-40c8-88fe-c63031686b70

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InjectiveOfIsCptGen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_ZarhinBundleKernelFirstCoordEquations

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.ProjCoord
open HomogeneousLocalization
variable {σ A Ω : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  [Field Ω]
namespace GlobalTheory.CompanionTheory.Ar.ProjCoord
theorem _root_.solution (ψ : A →+* Ω) (f : A) (hf : ψ f ≠ 0) {d : ℕ} (hd : f ∈ 𝒜 d) (n : ℕ) (a : A)
    (ha : a ∈ 𝒜 (n • d)) : awayEval 𝒜 ψ f hf (Away.mk 𝒜 hd n a ha) = ψ a / ψ f ^ n := by
  simp only [awayEval, RingHom.coe_comp, Function.comp_apply, HomogeneousLocalization.algebraMap_apply,
    Away.val_mk]
  rw [Localization.awayLift_mk (v := (ψ f)⁻¹) (hv := mul_inv_cancel₀ hf), div_eq_mul_inv, inv_pow]
end GlobalTheory.CompanionTheory.Ar.ProjCoord
