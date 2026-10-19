-- Prove2me | solution 1 for OAI.Problem313.noise_loss_le_rpow
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T02:05:02.69737+00:00
-- url     : https://prove2.me/submissions/2d928c14-9da2-4354-b12d-8e9e99b468c5

import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOption
import Definitions.Def_OAI_Combinatorics_SharpThreshold_SupportDegree
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockCounting
import Definitions.Def_OAI_Combinatorics_SharpThreshold_GraphBlockCapture
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Permutation
import Definitions.Def_OAI_Combinatorics_SharpThreshold_InfluenceReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockRestrictionSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbits
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Probability
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierVariance
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RussoReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierDerivative
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BooleanDerivative
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RestrictionInfluence
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RestrictionMassSubtype

open OAI OAI.Problem313
universe u
theorem h313_sig {σ : ℝ} (hσ : 0 < σ) : σ * Real.log (4 / σ) ≤ 2 := by
  have h1 : Real.log (4/σ) = Real.log (2/σ) + Real.log 2 := by
    rw [← Real.log_mul (by positivity) (by norm_num)]; congr 1; ring
  have h2 := Real.log_le_sub_one_of_pos (show 0 < 2/σ by positivity)
  have h3 := Real.log_two_lt_d9
  rw [h1]
  have h4 : σ * (2/σ) = 2 := by field_simp
  nlinarith

theorem solution {σ m : ℝ} (hσ : 0 < σ)
    (hσhalf : σ ≤ 1 / 2) (hm : 1 ≤ m) :
    (σ / 4) ^ (-(2 : ℝ) * (σ * Real.log m / 64)) ≤ m ^ (1 / 16 : ℝ) := by
  have hm0 : 0 < m := by linarith
  have hlm : 0 ≤ Real.log m := Real.log_nonneg hm
  have hs := h313_sig hσ
  rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos hm0]
  apply Real.exp_le_exp.mpr
  have : Real.log (σ/4) = - Real.log (4/σ) := by
    rw [← Real.log_inv]; congr 1; field_simp
  rw [this]
  nlinarith [mul_le_mul_of_nonneg_right hs hlm]

