-- Prove2me | solution 1 for OAI.Problem313.quadratic_mul_exp_neg_eighth_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T02:03:34.962333+00:00
-- url     : https://prove2.me/submissions/d34bddfc-6aae-4561-884c-869db936b5d2

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

open OAI OAI.Problem313


theorem solution (t : ℝ) (ht : 0 ≤ t) :
    t ^ 2 * Real.exp (-t / 8) ≤ 256 := by
  have h := Real.pow_div_factorial_le_exp (x := t/8) (by positivity) 2
  have he : Real.exp (-t/8) * Real.exp (t/8) = 1 := by rw [← Real.exp_add]; ring_nf; simp
  have hpos := Real.exp_pos (-t/8)
  simp only [Nat.factorial, Nat.cast_ofNat] at h
  norm_num at h
  have h2 := mul_le_mul_of_nonneg_left h hpos.le
  nlinarith

