-- Prove2me | solution 1 for GlobalTheory.isMinimal_of_forall_div_pow_twelve
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:04:59.671803+00:00
-- url     : https://prove2.me/submissions/173f7f77-672c-4839-b926-bb8dfdc34667

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsMinimalOfForallDivPowTwelve

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain WeierstrassCurve
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (R F : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field F] [Algebra R F] [IsFractionRing R F]
    (W : WeierstrassCurve F) (hI : W.IsIntegral R)
    (h : ∀ x : R, x ≠ 0 → W.Δ / algebraMap R F x ^ 12 ∈ (algebraMap R F).range → IsUnit x) :
    W.IsMinimal R := by
  refine ⟨⟨by simpa using hI, fun C hC _ => ?_⟩⟩
  simp only [one_smul]
  have hC' : (C • W).IsIntegral R := hC
  rw [← Subtype.coe_le_coe]
  rw [valuation_Δ_aux_eq_of_isIntegral, valuation_Δ_aux_eq_of_isIntegral]
  set v := HeightOneSpectrum.valuation F (IsDiscreteValuationRing.maximalIdeal R) with hv
  have hle : ∀ r : R, v (algebraMap R F r) ≤ 1 := fun r =>
    HeightOneSpectrum.valuation_le_one (K := F) (IsDiscreteValuationRing.maximalIdeal R) r
  rw [variableChange_Δ, map_mul, map_pow]
  refine mul_le_of_le_one_left' (pow_le_one' ?_ _)
  rcases ValuationRing.isInteger_or_isInteger R (C.u : F) with ⟨x, hx⟩ | ⟨x, hx⟩
  · have hx0 : x ≠ 0 := by
      rintro rfl
      exact C.u.ne_zero (by simpa using hx.symm)
    obtain ⟨r, hr⟩ := Δ_integral_of_isIntegral R (C • W)
    have hu : IsUnit x := h x hx0 ⟨r, by
      rw [hr, variableChange_Δ, hx, Units.val_inv_eq_inv_val, inv_pow, div_eq_inv_mul]⟩
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    have : ((C.u⁻¹ : Fˣ) : F) = algebraMap R F y := by
      rw [Units.val_inv_eq_inv_val, ← hx]
      exact (eq_inv_of_mul_eq_one_right (by rw [← map_mul, hy, map_one])).symm
    rw [this]
    exact hle y
  · rw [Units.val_inv_eq_inv_val, ← hx]
    exact hle x
end GlobalTheory
