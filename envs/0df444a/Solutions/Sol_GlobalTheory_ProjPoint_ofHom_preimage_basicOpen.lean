-- Prove2me | solution 1 for GlobalTheory.ProjPoint.ofHom_preimage_basicOpen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:47:17.089047+00:00
-- url     : https://prove2.me/submissions/1a50462e-c09a-44e6-b598-6160ba45ce58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_AwayLiftCompFromZeroRingHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory HomogeneousLocalization HomogeneousIdeal
universe u
noncomputable section
open GlobalTheory
open GlobalTheory.ProjPoint
variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {B C : Type u} [CommRing B] [CommRing C]
namespace GlobalTheory.ProjPoint
theorem _root_.solution (φ : A →+* B) (hφ : (irrelevant 𝒜).toIdeal.map φ = ⊤)
    {r : A} {n : ℕ} (hn : 0 < n) (hr : r ∈ 𝒜 n) :
    ofHom 𝒜 φ hφ ⁻¹ᵁ Proj.basicOpen 𝒜 r = PrimeSpectrum.basicOpen (φ r) := by
  rw [ofHom, Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ hn hr]
  exact basicOpen_eq_of_affine (R := .of B) (φ r)
end GlobalTheory.ProjPoint
