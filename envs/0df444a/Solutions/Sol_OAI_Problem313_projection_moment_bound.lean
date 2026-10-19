-- Prove2me | solution 1 for OAI.Problem313.projection_moment_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T02:04:45.385382+00:00
-- url     : https://prove2.me/submissions/fc2be6a2-529f-4f11-87e8-d4a6a5e3f62e

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
import Definitions.Def_OAI_Combinatorics_SharpThreshold_ProjectionIdentities

open OAI OAI.Problem313
universe u
open scoped BigOperators


theorem solution {M V H A : ℝ}
    (hM : 0 ≤ M) (hV : 0 ≤ V) (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hdual : M ≤ V ^ (3 / 4 : ℝ) * H ^ (1 / 4 : ℝ))
    (hfour : H ≤ A ^ 4 * M ^ 2) :
    M ≤ A ^ 2 * V ^ (3 / 2 : ℝ) := by
  have h1 : H ^ (1/4:ℝ) ≤ A * Real.sqrt M := by
    calc H ^ (1/4:ℝ) ≤ (A^4 * M^2) ^ (1/4:ℝ) := Real.rpow_le_rpow hH hfour (by norm_num)
      _ = A * Real.sqrt M := by
        rw [Real.mul_rpow (by positivity) (by positivity), Real.sqrt_eq_rpow, ← Real.rpow_natCast A 4,
          ← Real.rpow_natCast M 2, ← Real.rpow_mul hA, ← Real.rpow_mul hM]; norm_num
  have hs : Real.sqrt M ^ 2 = M := Real.sq_sqrt hM
  have hv : V ^ (3/2:ℝ) = (V^(3/4:ℝ))^2 := by rw [← Real.rpow_natCast, ← Real.rpow_mul hV]; norm_num
  have hV0 : 0 ≤ V^(3/4:ℝ) := by positivity
  have h2 : M ≤ V^(3/4:ℝ) * (A * Real.sqrt M) := le_trans hdual (mul_le_mul_of_nonneg_left h1 hV0)
  rw [hv]
  have hs0 := Real.sqrt_nonneg M
  rcases eq_or_lt_of_le hs0 with h0 | hpos
  · rw [← h0] at hs; rw [← hs]; norm_num; positivity
  · have h3 : Real.sqrt M ≤ V^(3/4:ℝ) * A := by nlinarith
    nlinarith [mul_le_mul h3 h3 hs0 (by positivity)]

