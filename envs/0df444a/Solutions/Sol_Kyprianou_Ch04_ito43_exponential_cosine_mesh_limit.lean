-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_exponential_cosine_mesh_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:54:16.04141+00:00
-- url     : https://prove2.me/submissions/b8010e52-06e1-40c1-8812-1ebfa4c96703

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_ito43_exponential_cosine_mesh_error_bound
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution (T : NNReal) (z : ℂ) :
    Tendsto (fun n : ℕ => (n:ℝ)*(1-(Complex.exp
      (((((T/(n:NNReal)):NNReal):ℝ):ℂ)*z)).re)) atTop (nhds (-(T:ℝ)*z.re)) := by
  let C : ℝ := (T:ℝ)*‖z‖
  have hsmall : Tendsto (fun n : ℕ => C/(n:ℝ)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat C
  have hlim : Tendsto (fun n : ℕ => C^2/(n:ℝ)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  apply Metric.tendsto_atTop.mpr
  intro e he
  have hgood := (hsmall.eventually (Iic_mem_nhds (by norm_num : (0:ℝ)<1))).and
    (hlim.eventually (Iio_mem_nhds he))
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hgood.and (eventually_gt_atTop (0:ℕ)))
  refine ⟨N,fun n hn => ?_⟩
  obtain ⟨⟨hs,he'⟩,hn0⟩ := hN n hn
  rw [Real.dist_eq]
  exact (Kyprianou.Ch04.ito43_exponential_cosine_mesh_error_bound T z n hn0 hs).trans_lt he'
