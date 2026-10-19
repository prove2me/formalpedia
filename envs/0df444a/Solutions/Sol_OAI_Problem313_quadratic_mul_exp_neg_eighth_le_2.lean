-- Prove2me | solution 2 for OAI.Problem313.quadratic_mul_exp_neg_eighth_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:38:11.586118+00:00
-- url     : https://prove2.me/submissions/1bfc8b87-67ff-45c9-8849-97ea8cf64e4f

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/ExpQuadratic.lean:L9-L29
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.quadratic_mul_exp_neg_eighth_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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

-- ---- from OAI.Combinatorics.SharpThreshold.ExpQuadratic ----
namespace OAI

noncomputable section

namespace Problem313

/-- A deliberately generous quadratic-exponential estimate. -/
lemma quadratic_mul_exp_neg_eighth_le (t : ℝ) (ht : 0 ≤ t) :
    t ^ 2 * Real.exp (-t / 8) ≤ 256 := by
  have hlin : t / 16 ≤ Real.exp (t / 16) := by
    have h := Real.add_one_le_exp (t / 16)
    linarith
  have hsquare : (t / 16) ^ 2 ≤ (Real.exp (t / 16)) ^ 2 := by
    exact pow_le_pow_left₀ (by positivity) hlin 2
  have hexp : (Real.exp (t / 16)) ^ 2 = Real.exp (t / 8) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hexp] at hsquare
  have hquad : t ^ 2 ≤ 256 * Real.exp (t / 8) := by
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hquad (le_of_lt (Real.exp_pos (-t / 8)))
  have hcancel : Real.exp (t / 8) * Real.exp (-t / 8) = 1 := by
    rw [← Real.exp_add]
    have hzero : t / 8 + -t / 8 = 0 := by ring
    rw [hzero, Real.exp_zero]
  nlinarith [hcancel]

end Problem313

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313


theorem solution : type_of% @_root_.OAI.Problem313.quadratic_mul_exp_neg_eighth_le := @_root_.OAI.Problem313.quadratic_mul_exp_neg_eighth_le
