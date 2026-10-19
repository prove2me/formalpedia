-- Prove2me | solution 1 for OAI.Problem313.variance_from_fourier_capture
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T02:10:10.810984+00:00
-- url     : https://prove2.me/submissions/6eabc63a-3f41-41e1-9861-6dc640fe3ba6

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
universe u
theorem h313_vfc {ι : Type u} [Fintype ι] [DecidableEq ι]
    (coeff : Finset ι → ℝ) (variance sigma ell influence lowConstant : ℝ)
    (hsigma : 0 < sigma) (hell : 0 < ell)
    (hvariance : variance = ∑ S : Finset ι with S.Nonempty, coeff S ^ 2)
    (hdirichlet : (∑ S : Finset ι, (S.card : ℝ) * coeff S ^ 2) = sigma ^ 2 * influence)
    (hcapture : (∑ S : Finset ι with S.Nonempty ∧
        (S.card : ℝ) ≤ (sigma * ell / 64) ^ 2 / 2, coeff S ^ 2)
      ≤ lowConstant * influence) :
    variance ≤ (lowConstant + 8192 / ell ^ 2) * influence := by
  have hK : 0 < (sigma * ell / 64)^2/2 := by positivity
  have h1 : variance ≤ (∑ S : Finset ι with S.Nonempty ∧ (S.card:ℝ) ≤ (sigma*ell/64)^2/2, coeff S ^ 2)
      + (∑ S : Finset ι, (S.card:ℝ) * coeff S ^ 2) / ((sigma*ell/64)^2/2) := by
    rw [hvariance, Finset.sum_filter, Finset.sum_filter, Finset.sum_div, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro S _
    have hc := sq_nonneg (coeff S)
    have hq : 0 ≤ (S.card:ℝ) * coeff S ^ 2 / ((sigma*ell/64)^2/2) := by positivity
    by_cases hne : S.Nonempty
    · by_cases hk : (S.card:ℝ) ≤ (sigma*ell/64)^2/2
      · rw [if_pos hne, if_pos ⟨hne, hk⟩]; linarith
      · push_neg at hk
        rw [if_pos hne, if_neg (fun h => absurd h.2 (not_le.mpr hk)), zero_add, le_div_iff₀ hK]; nlinarith
    · rw [if_neg hne, if_neg (fun h => hne h.1)]; linarith
  have h2 : sigma^2 * influence / ((sigma*ell/64)^2/2) = 8192 / ell^2 * influence := by
    field_simp; ring
  rw [hdirichlet, h2] at h1; linarith

theorem solution {ι : Type u} [Fintype ι] [DecidableEq ι]
    (coeff : Finset ι → ℝ) (variance sigma ell influence lowConstant : ℝ)
    (hsigma : 0 < sigma) (hell : 0 < ell)
    (hvariance : variance = ∑ S : Finset ι with S.Nonempty, coeff S ^ 2)
    (hdirichlet : (∑ S : Finset ι, (S.card : ℝ) * coeff S ^ 2) = sigma ^ 2 * influence)
    (hcapture : (∑ S : Finset ι with S.Nonempty ∧
        (S.card : ℝ) ≤ (sigma * ell / 64) ^ 2 / 2, coeff S ^ 2)
      ≤ lowConstant * influence) :
    variance ≤ (lowConstant + 8192 / ell ^ 2) * influence := by
  exact h313_vfc coeff variance sigma ell influence lowConstant hsigma hell hvariance hdirichlet hcapture

