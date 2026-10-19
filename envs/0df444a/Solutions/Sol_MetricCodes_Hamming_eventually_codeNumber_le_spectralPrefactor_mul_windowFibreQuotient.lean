-- Prove2me | solution 1 for MetricCodes.Hamming.eventually_codeNumber_le_spectralPrefactor_mul_windowFibreQuotient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:29.660979+00:00
-- url     : https://prove2.me/submissions/82eff8a6-4d17-4de5-9208-ed66997b34eb

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_eventually_transverse_add_le_longitudinal
import Theorems.Thm_MetricCodes_Hamming_longitudinalDegree_le_half
import Theorems.Thm_MetricCodes_Hamming_ceil_distance_pos
import Theorems.Thm_MetricCodes_Hamming_windowFibreQuotient_pos_of_fit
import Theorems.Thm_MetricCodes_Hamming_spectralGap_pos
import Theorems.Thm_MetricCodes_Hamming_eventually_topEigenvalue_uniform_gap_ceil
import Theorems.Thm_MetricCodes_Hamming_eventually_hamming_prefactor_le
import Theorems.Thm_MetricCodes_Hamming_finite_bound

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
set_option autoImplicit false
open Filter Metric Topology
open scoped BigOperators InnerProductSpace Topology
open MetricCodes.Hamming
namespace MetricCodes.Hamming
theorem _root_.solution
    {δ a b : ℝ} (hδ : 0 < δ) (hδ' : δ < (1 : ℝ) / 2)
    (h : Feasible δ a b) :
    ∀ᶠ n : ℕ in atTop,
      (codeNumber n (Nat.ceil (δ * (n : ℝ))) : ℝ) ≤
        spectralPrefactor δ a b * windowFibreQuotient a b n := by
  have hδone : δ ≤ 1 := by linarith
  filter_upwards [
    eventually_gt_atTop (0 : ℕ),
    eventually_transverse_add_le_longitudinal h.1 h.2.1 1,
    eventually_topEigenvalue_uniform_gap_ceil hδ.le h,
    eventually_hamming_prefactor_le hδ.le hδone h]
    with n hn hfit hmargin hprefactor
  have hkL : transverseDegree b n < longitudinalDegree a n := by
    omega
  have hhalf := longitudinalDegree_le_half h.2.2.1 n
  have hLn :
      longitudinalDegree a n + transverseDegree b n ≤ n := by
    omega
  have hd : 0 < Nat.ceil (δ * (n : ℝ)) :=
    ceil_distance_pos hδ hn
  have hgap :
      threshold n (Nat.ceil (δ * (n : ℝ))) <
        topEigenvalue n (transverseDegree b n)
          (longitudinalDegree a n) := by
    have hpositive := spectralGap_pos h
    linarith
  have hfinite := finite_bound hn hd hkL hLn hgap
  have hquotient : 0 ≤ windowFibreQuotient a b n :=
    (windowFibreQuotient_pos_of_fit h.2.2.1 hkL.le).le
  calc
    (codeNumber n (Nat.ceil (δ * (n : ℝ))) : ℝ) ≤
        ((1 - threshold n (Nat.ceil (δ * (n : ℝ)))) /
          (topEigenvalue n (transverseDegree b n)
            (longitudinalDegree a n) -
              threshold n (Nat.ceil (δ * (n : ℝ))))) *
            windowFibreQuotient a b n := by
      simpa [windowFibreQuotient] using hfinite
    _ ≤ spectralPrefactor δ a b * windowFibreQuotient a b n :=
      mul_le_mul_of_nonneg_right hprefactor hquotient
end MetricCodes.Hamming
