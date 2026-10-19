-- Prove2me | solution 2 for OAI.Problem313.projection_moment_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:21:05.876993+00:00
-- url     : https://prove2.me/submissions/abdfa1a0-4fb1-4d09-9aa8-65a614319a84

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/ProjectionNorm.lean:L60-L90
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.projection_moment_bound. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_SharpThreshold_ProjectionIdentities

-- ---- from OAI.Combinatorics.SharpThreshold.ProjectionNorm ----
namespace OAI

universe u

noncomputable section
open scoped BigOperators
namespace Problem313

/-- The scalar cancellation behind the `L⁴` duality argument. -/
theorem projection_moment_bound {M V H A : ℝ}
    (hM : 0 ≤ M) (hV : 0 ≤ V) (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hdual : M ≤ V ^ (3 / 4 : ℝ) * H ^ (1 / 4 : ℝ))
    (hfour : H ≤ A ^ 4 * M ^ 2) :
    M ≤ A ^ 2 * V ^ (3 / 2 : ℝ) := by
  have hroot : H ^ (1 / 4 : ℝ) ≤ A * M ^ (1 / 2 : ℝ) := by
    calc
      _ ≤ (A ^ 4 * M ^ 2) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow hH hfour (by norm_num)
      _ = A * M ^ (1 / 2 : ℝ) := by
        rw [Real.mul_rpow (pow_nonneg hA _) (sq_nonneg M),
          ← Real.rpow_natCast_mul hA, ← Real.rpow_natCast_mul hM]
        norm_num
  have hv : 0 ≤ V ^ (3 / 4 : ℝ) := Real.rpow_nonneg hV _
  have hs : 0 ≤ M ^ (1 / 2 : ℝ) := Real.rpow_nonneg hM _
  have hs2 : (M ^ (1 / 2 : ℝ)) ^ 2 = M := by
    rw [← Real.rpow_mul_natCast hM]
    norm_num
  have hbound : M ≤ (A * V ^ (3 / 4 : ℝ)) * M ^ (1 / 2 : ℝ) := by
    calc
      _ ≤ V ^ (3 / 4 : ℝ) * H ^ (1 / 4 : ℝ) := hdual
      _ ≤ V ^ (3 / 4 : ℝ) * (A * M ^ (1 / 2 : ℝ)) := mul_le_mul_of_nonneg_left hroot hv
      _ = _ := by ring
  have hsbound : M ^ (1 / 2 : ℝ) ≤ A * V ^ (3 / 4 : ℝ) := by
    nlinarith [mul_nonneg hA hv]
  have hsq := pow_le_pow_left₀ hs hsbound 2
  have hv2 : (V ^ (3 / 4 : ℝ)) ^ 2 = V ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_mul_natCast hV]
    norm_num
  simpa only [hs2, mul_pow, hv2] using hsq

end Problem313

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Problem313.projection_moment_bound := @_root_.OAI.Problem313.projection_moment_bound
