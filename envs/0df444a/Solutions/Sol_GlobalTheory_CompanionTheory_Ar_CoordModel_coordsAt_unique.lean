-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.CoordModel.coordsAt_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:30:57.027207+00:00
-- url     : https://prove2.me/submissions/8885cb6a-e0e9-4ec1-a3f7-d5b53c843377

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsCoordsAtOfCoordTie
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordModel_valAt_unique
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordModel_valAt_mul

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
theorem _root_.solution {K : Type} {ι : K → Type} {y : (Σ k, ι k) → Ω} (hξ : IsCptGen ξ) {w w' : (Σ k, ι k) → R}
    (h : CoordsAt ξ y z w) (h' : CoordsAt ξ y z w') (k : K) : ∃ u : Rˣ, ∀ i, w' ⟨k, i⟩ = u * w ⟨k, i⟩ := by
  obtain ⟨c, hc⟩ := h.1 k
  obtain ⟨d, hd⟩ := h'.1 k
  obtain ⟨hc0, hv⟩ := h.2 k c hc
  obtain ⟨hd0, hv'⟩ := h'.2 k d hd
  obtain ⟨r, hr, -⟩ := hv d
  obtain ⟨r', hr', e'⟩ := hv' c
  have h1 : ValAt ξ z 1 1 := ⟨hr.1, 1, map_one _, map_one _⟩
  have h2 := valAt_mul hr hr'
  rw [show y ⟨k, d⟩ / y ⟨k, c⟩ * (y ⟨k, c⟩ / y ⟨k, d⟩) = 1 by field_simp] at h2
  have hu : IsUnit (w' ⟨k, c⟩) := by
    rw [e']
    exact (IsUnit.of_mul_eq_one_right r (valAt_unique hξ h2 h1)).mul hd
  obtain ⟨-, hv''⟩ := h'.2 k c hu
  refine ⟨hu.unit * hc.unit⁻¹, fun i => ?_⟩
  obtain ⟨s, hs, es⟩ := hv i
  obtain ⟨s', hs', es'⟩ := hv'' i
  rw [es, es', valAt_unique hξ hs' hs, Units.val_mul, IsUnit.unit_spec, mul_assoc, mul_left_comm _ s,
    IsUnit.val_inv_mul, mul_one, mul_comm]
end GlobalTheory.CompanionTheory.Ar.CoordModel
