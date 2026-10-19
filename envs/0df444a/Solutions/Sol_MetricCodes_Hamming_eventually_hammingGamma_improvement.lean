-- Prove2me | solution 1 for MetricCodes.Hamming.eventually_hammingGamma_improvement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.946406+00:00
-- url     : https://prove2.me/submissions/c15e5193-385f-492b-a069-2f65cf4737b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_hammingGamma_zero
import Theorems.Thm_MetricCodes_Hamming_improvementSlope_gt_one
import Theorems.Thm_MetricCodes_Hamming_tendsto_improvementPath_zero
import Theorems.Thm_MetricCodes_Hamming_spectralMarginPolynomial_factor
import Theorems.Thm_MetricCodes_Hamming_spectralMarginPolynomial_continuous
import Theorems.Thm_MetricCodes_Hamming_spectralMarginPolynomial_improvement_zero

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
set_option autoImplicit false
open Filter Metric Topology
open scoped BigOperators InnerProductSpace Topology
open MetricCodes.Hamming
namespace MetricCodes.Hamming
theorem _root_.solution {a : ℝ}
    (ha : 0 < a) (ha' : a < (1 : ℝ) / 2) :
    ∀ᶠ b : ℝ in 𝓝[>] 0,
      MetricCodes.hammingGamma a 0 <
        MetricCodes.hammingGamma (improvementPath a b) b := by
  have hzero : 0 < spectralMarginPolynomial a (improvementSlope a) 0 := by
    rw [spectralMarginPolynomial_improvement_zero ha']
    have ha1 : 0 < 1 - a := by linarith
    have hhalf : 0 < 1 - 2 * a := by linarith
    exact mul_pos (mul_pos ha ha1) hhalf
  have hpoly :
      ∀ᶠ b : ℝ in 𝓝[>] 0,
        0 < spectralMarginPolynomial a (improvementSlope a) b := by
    have hcontinuous :
        ContinuousAt
          (spectralMarginPolynomial a (improvementSlope a)) 0 :=
      (spectralMarginPolynomial_continuous a (improvementSlope a)).continuousAt
    have hlim := hcontinuous.tendsto
    exact nhdsWithin_le_nhds (hlim.eventually (lt_mem_nhds hzero))
  have hhalf :
      ∀ᶠ b : ℝ in 𝓝[>] 0,
        improvementPath a b < (1 : ℝ) / 2 :=
    (tendsto_improvementPath_zero a).eventually (gt_mem_nhds ha')
  have hc : 1 < improvementSlope a := improvementSlope_gt_one ha'
  filter_upwards [hpoly, hhalf, self_mem_nhdsWithin]
    with b hbpoly hbhalf (hb : 0 < b)
  have hbpath : b < improvementPath a b := by
    unfold improvementPath
    nlinarith [mul_pos (sub_pos.mpr hc) hb]
  have hpath : 0 < improvementPath a b := lt_trans hb hbpath
  have hpath1 : improvementPath a b < 1 :=
    hbhalf.trans (by norm_num)
  have htail : 0 < 1 - improvementPath a b - b := by
    linarith
  have hbase : 0 < a * (1 - a) := mul_pos ha (by linarith)
  have hrad : 0 < improvementPath a b * (1 - improvementPath a b) :=
    mul_pos hpath (sub_pos.mpr hpath1)
  have hfactor :
      ((improvementPath a b - b) *
        (1 - improvementPath a b - b)) ^ 2 -
        (a * (1 - a)) *
          (improvementPath a b * (1 - improvementPath a b)) =
        b * spectralMarginPolynomial a (improvementSlope a) b := by
    simpa [improvementPath] using
      spectralMarginPolynomial_factor a (improvementSlope a) b
  have hmargin :
      0 < ((improvementPath a b - b) *
        (1 - improvementPath a b - b)) ^ 2 -
        (a * (1 - a)) *
          (improvementPath a b * (1 - improvementPath a b)) := by
    rw [hfactor]
    exact mul_pos hb hbpoly
  have htarget :
      0 < (improvementPath a b - b) *
        (1 - improvementPath a b - b) :=
    mul_pos (sub_pos.mpr hbpath) htail
  have hsquare :
      (Real.sqrt (a * (1 - a)) *
        Real.sqrt (improvementPath a b *
          (1 - improvementPath a b))) ^ 2 =
        (a * (1 - a)) *
          (improvementPath a b * (1 - improvementPath a b)) := by
    rw [mul_pow, Real.sq_sqrt hbase.le, Real.sq_sqrt hrad.le]
  have hroot :
      Real.sqrt (a * (1 - a)) *
          Real.sqrt (improvementPath a b *
            (1 - improvementPath a b)) <
        (improvementPath a b - b) *
          (1 - improvementPath a b - b) := by
    have hnonneg :
        0 ≤ Real.sqrt (a * (1 - a)) *
          Real.sqrt (improvementPath a b *
            (1 - improvementPath a b)) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith
  have hquot :
      Real.sqrt (a * (1 - a)) <
        ((improvementPath a b - b) *
          (1 - improvementPath a b - b)) /
            Real.sqrt
              (improvementPath a b * (1 - improvementPath a b)) :=
    (lt_div_iff₀ (Real.sqrt_pos.2 hrad)).2 hroot
  rw [hammingGamma_zero ha (by linarith)]
  unfold MetricCodes.hammingGamma
  calc
    2 * Real.sqrt (a * (1 - a)) <
        2 * (((improvementPath a b - b) *
          (1 - improvementPath a b - b)) /
            Real.sqrt
              (improvementPath a b * (1 - improvementPath a b))) :=
      mul_lt_mul_of_pos_left hquot (by norm_num)
    _ = 2 * (improvementPath a b - b) *
        (1 - improvementPath a b - b) /
          Real.sqrt
            (improvementPath a b * (1 - improvementPath a b)) := by ring
end MetricCodes.Hamming
