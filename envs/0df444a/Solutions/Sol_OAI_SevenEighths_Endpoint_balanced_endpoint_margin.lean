-- Prove2me | solution 1 for OAI.SevenEighths.Endpoint.balanced_endpoint_margin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:59:28.399631+00:00
-- url     : https://prove2.me/submissions/f5854b74-30f3-4ee3-af90-a111b0f8cc78

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_NumberTheory_DirichletL_Endpoint
import Theorems.Thm_OAI_SevenEighths_Endpoint_balanceDenominator_bounds
import Theorems.Thm_OAI_SevenEighths_Endpoint_endpoint_identity

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.Endpoint
noncomputable section
namespace OAI.SevenEighths.Endpoint
theorem _root_.solution {δ y : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 5 / 6) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) :
    (49 : ℝ) / 440640 ≤ -balancedExponent δ y := by
  obtain ⟨hJlo, hJhi⟩ := balanceDenominator_bounds hδ0 hδ1 hy0 hy1
  have hJpos : 0 < balanceDenominator δ y := by linarith
  have hvpos : 0 < certificateWeight y := by dsimp [certificateWeight]; linarith
  have hinner : 0 ≤ (1 + 3 * y) * (15 + 32 * y) * δ + 9 - 13 * y := by
    have hp : 0 ≤ (1 + 3 * y) * (15 + 32 * y) * δ := by positivity
    linarith
  have hrest : 0 ≤ 4 * y * (4 * certificateWeight y * δ *
      ((1 + 3 * y) * (15 + 32 * y) * δ + 9 - 13 * y) + 265 + 3485 * y) := by
    positivity
  have hsq : 0 ≤ (3 + 5 * y) * (4 * certificateWeight y * δ - 79) ^ 2 := by
    positivity
  have hid := endpoint_identity δ y (ne_of_gt hJpos)
  have hcert : 49 * (3 + 5 * y) ≤
      10368 * certificateWeight y * balanceDenominator δ y * (-balancedExponent δ y) := by
    nlinarith only [hid, hrest, hsq]
  have hvhi : certificateWeight y ≤ 17 * (3 + 5 * y) := by
    dsimp [certificateWeight]
    linarith
  have hscaled : 49 * certificateWeight y ≤
      176256 * certificateWeight y * balanceDenominator δ y * (-balancedExponent δ y) := by
    nlinarith only [hcert, hvhi]
  have hcancel : 49 ≤ 176256 * balanceDenominator δ y * (-balancedExponent δ y) := by
    nlinarith only [hscaled, hvpos]
  have hEpos : 0 < -balancedExponent δ y := by
    by_contra hn
    have hn' : -balancedExponent δ y ≤ 0 := le_of_not_gt hn
    have hp := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hJpos) hn'
    nlinarith only [hcancel, hp]
  have hup := mul_le_mul_of_nonneg_right hJhi (le_of_lt hEpos)
  nlinarith only [hcancel, hup]
end OAI.SevenEighths.Endpoint
