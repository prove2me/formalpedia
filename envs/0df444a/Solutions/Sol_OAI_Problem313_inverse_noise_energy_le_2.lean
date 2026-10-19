-- Prove2me | solution 2 for OAI.Problem313.inverse_noise_energy_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:16:07.723213+00:00
-- url     : https://prove2.me/submissions/368d82a3-9748-468b-bf36-ecf3f28868db

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/LowDegreeL4.lean:L13-L33
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.inverse_noise_energy_le. The node keeps its source
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

-- ---- from OAI.Combinatorics.SharpThreshold.LowDegreeL4 ----
namespace OAI

universe u v

noncomputable section

namespace Problem313

open scoped BigOperators

/-- Removing a diagonal noise multiplier costs at most `rho ^ (-2*k)`
in squared coefficient norm on coefficients supported in degrees at most `k`. -/
theorem inverse_noise_energy_le {ι : Type u} [Fintype ι]
    (degree : ι → ℕ) (c : ι → ℝ) (rho k : ℝ)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hdegree : ∀ i, c i ≠ 0 → (degree i : ℝ) ≤ k) :
    (∑ i, (rho ^ (-(degree i : ℝ)) * c i) ^ 2) ≤
      rho ^ (-2 * k) * ∑ i, (c i) ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hc : c i = 0
  · simp [hc]
  have hexp : -2 * k ≤ -(degree i : ℝ) * 2 := by
    linarith [hdegree i hc]
  have hrpow := Real.rpow_le_rpow_of_exponent_ge hrho hrho1 hexp
  have hsq : (rho ^ (-(degree i : ℝ))) ^ 2 =
      rho ^ (-(degree i : ℝ) * 2) := by
    rw [Real.rpow_mul hrho.le, Real.rpow_two]
  rw [mul_pow, hsq]
  exact mul_le_mul_of_nonneg_right hrpow (sq_nonneg (c i))

end Problem313

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313
open scoped BigOperators


theorem solution.{u} : type_of% @_root_.OAI.Problem313.inverse_noise_energy_le.{u} := @_root_.OAI.Problem313.inverse_noise_energy_le.{u}
