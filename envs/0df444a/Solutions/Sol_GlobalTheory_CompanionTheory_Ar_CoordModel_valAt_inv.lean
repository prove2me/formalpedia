-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.CoordModel.valAt_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:09:15.593536+00:00
-- url     : https://prove2.me/submissions/6af6b960-e944-4a3e-b0f8-a018d5724059

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsCoordsAtOfCoordTie

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
theorem _root_.solution {a : Ω} {r : Rˣ} (h : ValAt ξ z a r) : a ≠ 0 ∧ ValAt ξ z a⁻¹ ↑r⁻¹ := by
  obtain ⟨hz, t, rfl, e⟩ := h
  have ht : IsUnit t := (Scheme.isLocalHom_stalkClosedPointTo' z).map_nonunit t (by have := r.isUnit; rw [← e] at this; exact this)
  obtain ⟨u, rfl⟩ := ht
  refine ⟨(u.isUnit.map (genMap ξ ⟨centre z, hz⟩)).ne_zero, hz, ↑u⁻¹, map_units_inv _ u, ?_⟩
  refine (Units.inv_eq_of_mul_eq_one_right ?_).symm
  rw [← e]
  exact (map_mul _ _ _).symm.trans ((congrArg _ u.mul_inv).trans (map_one _))
end GlobalTheory.CompanionTheory.Ar.CoordModel
