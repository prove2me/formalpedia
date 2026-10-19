-- Prove2me | solution 2 for OAI.Problem313.sigma_mul_log_four_div_le_two
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:01:17.967886+00:00
-- url     : https://prove2.me/submissions/4de71587-62a7-419e-baee-ac17291f9f9e

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/LowDegreeConstants.lean:L11-L36
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.sigma_mul_log_four_div_le_two. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RestrictionInfluence
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RestrictionMassSubtype

-- ---- from OAI.Combinatorics.SharpThreshold.LowDegreeConstants ----
namespace OAI

universe u

noncomputable section

namespace Problem313

/-- Uniform bias-dependent logarithmic bound used in the low-degree estimate. -/
theorem sigma_mul_log_four_div_le_two {σ : ℝ} (hσ : 0 < σ)
    (hσhalf : σ ≤ 1 / 2) : σ * Real.log (4 / σ) ≤ 2 := by
  have hσne : σ ≠ 0 := ne_of_gt hσ
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hinv : 0 < 1 / (2 * σ) := by positivity
  have hloginv := Real.log_le_sub_one_of_pos hinv
  have hlogsplit : Real.log (4 / σ) =
      3 * Real.log 2 + Real.log (1 / (2 * σ)) := by
    rw [Real.log_div (by norm_num) hσne,
      Real.log_div (by norm_num) (by positivity : 2 * σ ≠ 0),
      Real.log_mul (by norm_num) hσne]
    have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      have := Real.log_pow (2 : ℝ) 2
      norm_num at this
      exact this
    rw [hlog4, Real.log_one]
    ring
  have hscaled := mul_le_mul_of_nonneg_left hloginv (le_of_lt hσ)
  have hcancel : σ * (1 / (2 * σ) - 1) = 1 / 2 - σ := by
    field_simp
  rw [hcancel] at hscaled
  rw [hlogsplit]
  nlinarith [mul_le_mul_of_nonneg_left hlog2 (le_of_lt hσ)]

end Problem313

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313


theorem solution : type_of% @_root_.OAI.Problem313.sigma_mul_log_four_div_le_two := @_root_.OAI.Problem313.sigma_mul_log_four_div_le_two
