-- Prove2me | solution 2 for OAI.Problem313.noise_loss_le_rpow
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:03:54.418801+00:00
-- url     : https://prove2.me/submissions/7b75cc24-041f-4c77-a783-8819df512e28

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/LowDegreeConstants.lean:L38-L54
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.noise_loss_le_rpow. The node keeps its source
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
import Theorems.Thm_OAI_Problem313_sigma_mul_log_four_div_le_two

-- ---- from OAI.Combinatorics.SharpThreshold.LowDegreeConstants ----
namespace OAI

universe u

noncomputable section

namespace Problem313

/-- The noise loss has a uniformly small power of the orbit-size parameter. -/
theorem noise_loss_le_rpow {σ m : ℝ} (hσ : 0 < σ)
    (hσhalf : σ ≤ 1 / 2) (hm : 1 ≤ m) :
    (σ / 4) ^ (-(2 : ℝ) * (σ * Real.log m / 64)) ≤ m ^ (1 / 16 : ℝ) := by
  have hmpos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg hm
  have hσne : σ ≠ 0 := ne_of_gt hσ
  have hlogneg : Real.log (σ / 4) = -Real.log (4 / σ) := by
    rw [Real.log_div hσne (by norm_num), Real.log_div (by norm_num) hσne]
    ring
  rw [Real.rpow_def_of_pos (by positivity : 0 < σ / 4),
    Real.rpow_def_of_pos hmpos]
  apply Real.exp_le_exp.mpr
  rw [hlogneg]
  have hbound := sigma_mul_log_four_div_le_two hσ hσhalf
  have hmul := mul_le_mul_of_nonneg_right hbound hlogm
  nlinarith

end Problem313

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313


theorem solution : type_of% @_root_.OAI.Problem313.noise_loss_le_rpow := @_root_.OAI.Problem313.noise_loss_le_rpow
