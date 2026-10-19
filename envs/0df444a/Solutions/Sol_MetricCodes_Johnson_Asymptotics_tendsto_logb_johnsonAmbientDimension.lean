-- Prove2me | solution 1 for MetricCodes.Johnson.Asymptotics.tendsto_logb_johnsonAmbientDimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.299848+00:00
-- url     : https://prove2.me/submissions/b08355e6-e23f-4477-8bc7-b2a7e9a6f543

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_tendsto_logb_choose_longitudinal
import Theorems.Thm_MetricCodes_Hamming_tendsto_logb_hammingFibreDimension
import Theorems.Thm_MetricCodes_Johnson_AdmissibleDegrees_terminal_le_half
import Theorems.Thm_MetricCodes_Johnson_AsymptoticParameters_degree_pos
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_eventually_admissibleDegrees
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_terminalHarmonic_le_johnsonAmbientDimension
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_johnsonAmbientDimension_le_terminalChoose

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped Topology
open MetricCodes.Johnson.Asymptotics
namespace MetricCodes.Johnson.Asymptotics
theorem _root_.solution
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    Tendsto
      (fun n : ℕ =>
        Real.logb 2
          (MetricCodes.johnsonAmbientDimension n
            (supportDegree b n + complementDegree g n)
            (terminalDegree u n) : ℝ) /
              (n : ℝ))
      atTop (nhds (MetricCodes.binaryEntropy u)) := by
  have hu := h.degree_pos
  have huhalf : u ≤ (1 : ℝ) / 2 := by
    linarith [h.degree_lt_weight, h.weight_lt_half]
  have huone : u < 1 := by linarith
  have hterminal :
      Tendsto
        (fun n : ℕ =>
          Real.logb 2
            (MetricCodes.booleanHarmonicDimension n
              (terminalDegree u n) : ℝ) /
                (n : ℝ))
        atTop (nhds (MetricCodes.binaryEntropy u)) := by
    simpa [terminalDegree, MetricCodes.Hamming.transverseDegree,
      MetricCodes.Hamming.longitudinalDegree,
      MetricCodes.hammingFibreDimension] using
      MetricCodes.Hamming.tendsto_logb_hammingFibreDimension hu huhalf
  have hchoose :
      Tendsto
        (fun n : ℕ =>
          Real.logb 2
            (n.choose (terminalDegree u n) : ℝ) /
              (n : ℝ))
        atTop (nhds (MetricCodes.binaryEntropy u)) := by
    simpa [terminalDegree] using
      MetricCodes.Hamming.tendsto_logb_choose_longitudinal hu huone
  have hlower :
      ∀ᶠ n : ℕ in atTop,
        Real.logb 2
            (MetricCodes.booleanHarmonicDimension n
              (terminalDegree u n) : ℝ) /
                (n : ℝ) ≤
          Real.logb 2
            (MetricCodes.johnsonAmbientDimension n
              (supportDegree b n + complementDegree g n)
              (terminalDegree u n) : ℝ) /
                (n : ℝ) := by
    filter_upwards [eventually_admissibleDegrees h,
      eventually_gt_atTop (0 : ℕ)] with n hn hnpos
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
    have htermhalf : 2 * terminalDegree u n ≤ n := by
      have hhalf := hn.terminal_le_half
      omega
    have htermpos :
        0 < (MetricCodes.booleanHarmonicDimension n
          (terminalDegree u n) : ℝ) := by
      exact_mod_cast MetricCodes.Johnson.booleanHarmonicDimension_pos
        htermhalf
    apply (div_le_div_iff_of_pos_right hnreal).mpr
    apply Real.logb_le_logb_of_le
      (by norm_num : (1 : ℝ) < 2) htermpos
    exact_mod_cast terminalHarmonic_le_johnsonAmbientDimension hn
  have hupper :
      ∀ᶠ n : ℕ in atTop,
        Real.logb 2
            (MetricCodes.johnsonAmbientDimension n
              (supportDegree b n + complementDegree g n)
              (terminalDegree u n) : ℝ) /
                (n : ℝ) ≤
          Real.logb 2
            (n.choose (terminalDegree u n) : ℝ) /
              (n : ℝ) := by
    filter_upwards [eventually_admissibleDegrees h,
      eventually_gt_atTop (0 : ℕ)] with n hn hnpos
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
    have htermhalf : 2 * terminalDegree u n ≤ n := by
      have hhalf := hn.terminal_le_half
      omega
    have htermpos :
        0 < (MetricCodes.booleanHarmonicDimension n
          (terminalDegree u n) : ℝ) := by
      exact_mod_cast MetricCodes.Johnson.booleanHarmonicDimension_pos
        htermhalf
    have hambientpos :
        0 < (MetricCodes.johnsonAmbientDimension n
          (supportDegree b n + complementDegree g n)
          (terminalDegree u n) : ℝ) := by
      have hle := terminalHarmonic_le_johnsonAmbientDimension hn
      exact lt_of_lt_of_le htermpos (by exact_mod_cast hle)
    apply (div_le_div_iff_of_pos_right hnreal).mpr
    apply Real.logb_le_logb_of_le
      (by norm_num : (1 : ℝ) < 2) hambientpos
    exact_mod_cast johnsonAmbientDimension_le_terminalChoose hn
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hterminal hchoose hlower hupper
end MetricCodes.Johnson.Asymptotics
