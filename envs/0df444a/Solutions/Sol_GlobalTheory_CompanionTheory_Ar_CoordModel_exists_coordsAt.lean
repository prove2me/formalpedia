-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.CoordModel.exists_coordsAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:16:02.452515+00:00
-- url     : https://prove2.me/submissions/aa1a22ff-0842-498e-a698-d324994f82f7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsCoordsAtOfCoordTie
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordModel_valAt_unique
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordModel_valAt_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordModel_valAt_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.CoordModel
open AlgebraicGeometry CategoryTheory
variable (A : Type) [CommRing A] (Ω : Type) [Field Ω] [Algebra A Ω]
variable [IsDomain A] [IsFractionRing A Ω]
variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {R : Type} [CommRing R] [IsLocalRing R]
  {ξ : Spec (CommRingCat.of Ω) ⟶ X} {z : Spec (CommRingCat.of R) ⟶ X}
namespace GlobalTheory.CompanionTheory.Ar.CoordModel
theorem _root_.solution {K : Type} {ι : K → Type} (y : (Σ k, ι k) → Ω) (hz : genPt ξ ⤳ centre z)
    (h : ∀ k, ∃ c, InChart ξ (fun i => y ⟨k, i⟩) c ⟨centre z, hz⟩) (hξ : IsCptGen ξ) :
    ∃ w, CoordsAt ξ y z w := by
  choose c hc using h
  have hv : ∀ j : Σ k, ι k, ∃ r, ValAt ξ z (y j / y ⟨j.1, c j.1⟩) r := by
    rintro ⟨k, i⟩
    obtain ⟨s, hs⟩ := (hc k).2 i
    exact ⟨_, hz, s, hs, rfl⟩
  choose w hw using hv
  refine ⟨w, fun k => ⟨c k, ?_⟩, fun k d hd => ?_⟩
  · have h1 : ValAt ξ z 1 1 := ⟨hz, 1, map_one _, map_one _⟩
    have h2 := hw ⟨k, c k⟩
    rw [div_self (hc k).1] at h2
    rw [valAt_unique hξ h2 h1]; exact isUnit_one
  · obtain ⟨u, hu⟩ := hd
    have h1 := hw ⟨k, d⟩
    rw [← hu] at h1
    obtain ⟨h0, h2⟩ := valAt_inv h1
    have hd0 : y ⟨k, d⟩ ≠ 0 := fun e => h0 (by simp [e])
    refine ⟨hd0, fun i => ⟨w ⟨k, i⟩ * ↑u⁻¹, ?_, by rw [← hu]; simp⟩⟩
    have h3 := valAt_mul (hw ⟨k, i⟩) h2
    have hc0 : y ⟨k, c k⟩ ≠ 0 := (hc k).1
    convert h3 using 1
    field_simp
end GlobalTheory.CompanionTheory.Ar.CoordModel
