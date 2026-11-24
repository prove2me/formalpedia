-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.ProjCoord.awayEval_comp_awayMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:18:45.2428+00:00
-- url     : https://prove2.me/submissions/eeaf526b-1aa7-4ed4-87df-063bc371d399

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InjectiveOfIsCptGen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_ZarhinBundleKernelFirstCoordEquations
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_ProjCoord_awayEval_mk

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
theorem _root_.solution (ψ : A →+* Ω) {f g x : A} {d e : ℕ} (hd : f ∈ 𝒜 d) (he : g ∈ 𝒜 e)
    (hx : x = f * g) (hf : ψ f ≠ 0) (h0 : ψ x ≠ 0) :
    (awayEval 𝒜 ψ x h0).comp (awayMap 𝒜 he hx) = awayEval 𝒜 ψ f hf := by
  refine RingHom.ext fun z => ?_
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hd z
  have hg : ψ g ≠ 0 := by
    rw [hx, map_mul] at h0
    exact right_ne_zero_of_mul h0
  rw [RingHom.comp_apply, awayMap_mk, awayEval_mk, awayEval_mk]
  subst hx
  simp only [map_mul, map_pow, mul_pow]
  field_simp
end GlobalTheory.CompanionTheory.Ar.ProjCoord
