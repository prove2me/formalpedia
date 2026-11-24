-- Prove2me | solution 1 for GlobalTheory.PeriodChange.change_of_normalisation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:21:19.617442+00:00
-- url     : https://prove2.me/submissions/f731586a-4e88-4eaf-83c5-1a067e1c4e7e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ChangeOfNormalisation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix NumberField
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodChange
open Complex Matrix NumberField
namespace GlobalTheory.PeriodChange
namespace _root_.GlobalTheory.PeriodChange
theorem _root_.solution {g : ℕ} (h h' τ' A B L R : Matrix (Fin g) (Fin g) ℂ)
    (hA : h * L = A) (hB : h * R = B) (hL : h' * L = 1) (hR : h' * R = τ') (hs : τ'.IsSymm)
    (hu : IsUnit h.det) :
    τ' = Bᵀ * (Aᵀ)⁻¹ ∧ h' = ((Aᵀ)⁻¹)ᵀ * h ∧ h.det = (Aᵀ).det * h'.det := by
  have hL' : L = h⁻¹ * A := by
    rw [← hA, ← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul]
  have hAh : h' * h⁻¹ * A = 1 := by rw [Matrix.mul_assoc, ← hL', hL]
  have hA1 : A * (h' * h⁻¹) = 1 := mul_eq_one_comm.mp hAh
  have hAu : IsUnit A.det := isUnit_det_of_right_inverse hA1
  have hAinv : A⁻¹ = h' * h⁻¹ := inv_eq_right_inv hA1
  have hh' : h' = A⁻¹ * h := by
    rw [hAinv, Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one]
  refine ⟨?_, ?_, ?_⟩
  · calc τ' = τ'ᵀ := hs.eq.symm
      _ = Bᵀ * (Aᵀ)⁻¹ := by
        rw [← hR, hh', Matrix.mul_assoc, hB, transpose_mul, transpose_nonsing_inv]
  · rw [← transpose_nonsing_inv, transpose_transpose]; exact hh'
  · have : h = A * h' := by
      rw [hh', ← Matrix.mul_assoc, mul_nonsing_inv _ hAu, Matrix.one_mul]
    conv_lhs => rw [this]
    rw [det_mul, det_transpose]
end _root_.GlobalTheory.PeriodChange
end GlobalTheory.PeriodChange
