-- Prove2me | solution 1 for MetricCodes.Hamming.tendsto_terminal_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.946406+00:00
-- url     : https://prove2.me/submissions/0caff8ee-6953-4cd0-8ed3-72320a6b4fda

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_tendsto_transverse_ratio
import Theorems.Thm_MetricCodes_Hamming_tendsto_terminal_degree_ratio
import Theorems.Thm_MetricCodes_Hamming_hammingJacobiEntry_eq_normalized
import Theorems.Thm_MetricCodes_Hamming_normalizedCoefficient_zero

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
set_option autoImplicit false
open Filter Metric Topology
open scoped BigOperators InnerProductSpace Topology
open MetricCodes.Hamming
namespace MetricCodes.Hamming
theorem _root_.solution {a b : ℝ}
    (ha : 0 < a) (ha' : a < 1) (hb : 0 ≤ b) (r : ℕ) :
    Tendsto
      (fun n : ℕ =>
        MetricCodes.hammingJacobiEntry n (transverseDegree b n)
          (longitudinalDegree a n - r))
      atTop (nhds (MetricCodes.hammingGamma a b / 2)) := by
  have hx := tendsto_terminal_degree_ratio ha r
  have hy := tendsto_transverse_ratio hb
  have hz := tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hnum := ((hx.sub hy).add hz).mul ((hone.sub hx).sub hy)
  have hrad := (hx.add hz).mul (hone.sub hx)
  have hroot := hrad.sqrt
  have hrootne : Real.sqrt (a * (1 - a)) ≠ 0 :=
    (Real.sqrt_pos.2 (mul_pos ha (sub_pos.mpr ha'))).ne'
  have pointwise_div {f g : ℕ → ℝ} {l : ℝ}
      (h : Tendsto (f / g) atTop (nhds l)) :
      Tendsto (fun n => f n / g n) atTop (nhds l) :=
    h.congr' (Filter.Eventually.of_forall (fun _ => rfl))
  have hnorm :
      Tendsto
        (fun n : ℕ => normalizedCoefficient
          (((longitudinalDegree a n - r : ℕ) : ℝ) / (n : ℝ))
          ((transverseDegree b n : ℝ) / (n : ℝ))
          ((1 : ℝ) / (n : ℝ)))
        atTop (nhds (normalizedCoefficient a b 0)) := by
    simpa [normalizedCoefficient] using
      pointwise_div (hnum.div hroot (by simpa using hrootne))
  rw [normalizedCoefficient_zero] at hnorm
  refine hnorm.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact (hammingJacobiEntry_eq_normalized n
    (transverseDegree b n) (longitudinalDegree a n - r) hn).symm
end MetricCodes.Hamming
