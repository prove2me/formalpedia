-- Prove2me | solution 1 for MetricCodes.Spherical.GeneralSpectral.tendsto_terminal_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.020426+00:00
-- url     : https://prove2.me/submissions/586ad356-2e71-4b0b-a9e8-532a1a247bc9

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_tendsto_transverse_ratio
import Theorems.Thm_MetricCodes_Hamming_tendsto_terminal_degree_ratio
import Theorems.Thm_SpherePacking_SpectralAsymptotics_jacobiCoefficient_eq_normalized
import Theorems.Thm_MetricCodes_Spherical_GeneralSpectral_tendsto_transverse_ratio
import Theorems.Thm_MetricCodes_Spherical_GeneralSpectral_tendsto_terminal_degree_ratio
import Theorems.Thm_MetricCodes_Spherical_GeneralSpectral_normalizedCoefficient_eq_Gamma

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open Filter Topology
open scoped BigOperators Nat Topology InnerProductSpace
open MetricCodes.Spherical.GeneralSpectral
namespace MetricCodes.Spherical.GeneralSpectral
theorem _root_.solution {a b : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (r : ℕ) :
    Tendsto
      (fun n : ℕ =>
        SpherePacking.Gegenbauer.jacobiCoefficient
          n (transverseDegree b n) (longitudinalDegree a n - r))
      atTop (nhds (MetricCodes.Gamma a b)) := by
  have hx := tendsto_terminal_degree_ratio ha r
  have hy := tendsto_transverse_ratio hb
  have hz : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ))
      atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have htwo : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2) :=
    tendsto_const_nhds
  have hnum := ((hx.sub hy).add hz).mul
    (((hx.add hy).add hone).sub (htwo.mul hz))
  have hrad := (((hx.add hz).mul
    ((hx.add hone).sub (htwo.mul hz))).mul
      (((htwo.mul hx).add hone).sub (htwo.mul hz))).mul
        ((htwo.mul hx).add hone)
  have hroot := hrad.sqrt
  have hrootne :
      Real.sqrt
        ((a + 0) * (a + 1 - 2 * 0) *
          (2 * a + 1 - 2 * 0) * (2 * a + 1)) ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.2
    have hone : 0 < a + 1 := by linarith
    have htwo : 0 < 2 * a + 1 := by linarith
    simpa using mul_pos (mul_pos (mul_pos ha hone) htwo) htwo
  have hnorm := hnum.div hroot hrootne
  have pointwise_div {f g : ℕ → ℝ} {l : ℝ}
      (h : Tendsto (f / g) atTop (nhds l)) :
      Tendsto (fun n => f n / g n) atTop (nhds l) :=
    h.congr' (Filter.Eventually.of_forall (fun _ => rfl))
  have hnorm' :
      Tendsto
        (fun n : ℕ =>
          SpherePacking.SpectralAsymptotics.normalizedCoefficient
            (((longitudinalDegree a n - r : ℕ) : ℝ) / (n : ℝ))
            ((transverseDegree b n : ℝ) / (n : ℝ))
            ((1 : ℝ) / (n : ℝ)))
        atTop
        (nhds
          (SpherePacking.SpectralAsymptotics.normalizedCoefficient a b 0)) := by
    simpa [SpherePacking.SpectralAsymptotics.normalizedCoefficient]
      using pointwise_div hnorm
  rw [normalizedCoefficient_eq_Gamma ha b] at hnorm'
  refine hnorm'.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact
    (SpherePacking.SpectralAsymptotics.jacobiCoefficient_eq_normalized
      n (transverseDegree b n) (longitudinalDegree a n - r) hn).symm
end MetricCodes.Spherical.GeneralSpectral
