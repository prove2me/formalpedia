-- Prove2me | solution 1 for OAI.Problem313.inverse_noise_energy_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T02:04:54.774763+00:00
-- url     : https://prove2.me/submissions/299d3ee7-bf9f-4ae6-a86f-aef0d9f011ea

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
universe u v
open scoped BigOperators


theorem solution {ι : Type u} [Fintype ι]
    (degree : ι → ℕ) (c : ι → ℝ) (rho k : ℝ)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hdegree : ∀ i, c i ≠ 0 → (degree i : ℝ) ≤ k) :
    (∑ i, (rho ^ (-(degree i : ℝ)) * c i) ^ 2) ≤
      rho ^ (-2 * k) * ∑ i, (c i) ^ 2 := by
  rw [Finset.mul_sum]; apply Finset.sum_le_sum; intro i _
  by_cases hc : c i = 0
  · simp [hc]
  · have hd := hdegree i hc
    have h1 : (rho ^ (-(degree i : ℝ)))^2 = rho ^ (-2 * (degree i:ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hrho.le]; congr 1; push_cast; ring
    have h2 : rho ^ (-2 * (degree i:ℝ)) ≤ rho ^ (-2*k) :=
      Real.rpow_le_rpow_of_exponent_ge hrho hrho1 (by linarith)
    rw [mul_pow, h1]; exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)

