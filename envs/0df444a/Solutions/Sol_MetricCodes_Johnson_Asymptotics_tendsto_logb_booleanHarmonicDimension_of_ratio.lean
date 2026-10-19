-- Prove2me | solution 1 for MetricCodes.Johnson.Asymptotics.tendsto_logb_booleanHarmonicDimension_of_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.299848+00:00
-- url     : https://prove2.me/submissions/5d38d7a8-8d97-4614-a097-ecd6f9c889b7

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_choose_le_mul_hammingFibreDimension
import Theorems.Thm_MetricCodes_Hamming_hammingFibreDimension_le_choose
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_tendsto_logb_choose_of_ratio
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_tendsto_logb_succ_of_le_dimension

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
    {N K : ℕ → ℕ} {a b : ℝ}
    (hN : Tendsto (fun n : ℕ => (N n : ℝ) / (n : ℝ))
      atTop (nhds a))
    (hK : Tendsto (fun n : ℕ => (K n : ℝ) / (n : ℝ))
      atTop (nhds b))
    (hb : 0 < b) (hba : b < a)
    (hhalf : ∀ᶠ n : ℕ in atTop, 2 * K n ≤ N n)
    (hNle : ∀ᶠ n : ℕ in atTop, N n ≤ n) :
    Tendsto
      (fun n : ℕ =>
        Real.logb 2
          (MetricCodes.booleanHarmonicDimension (N n) (K n) : ℝ) /
            (n : ℝ))
      atTop (nhds (a * MetricCodes.binaryEntropy (b / a))) := by
  have hKN : ∀ᶠ n : ℕ in atTop, K n ≤ N n :=
    hhalf.mono (fun _ hn => by omega)
  have hchoose :=
    tendsto_logb_choose_of_ratio hN hK hb hba hKN
  have hpoly := tendsto_logb_succ_of_le_dimension hNle
  have hlowerlimit :
      Tendsto
        (fun n : ℕ =>
          Real.logb 2 ((N n).choose (K n) : ℝ) / (n : ℝ) -
            Real.logb 2 ((N n + 1 : ℕ) : ℝ) / (n : ℝ))
        atTop (nhds (a * MetricCodes.binaryEntropy (b / a))) := by
    simpa using hchoose.sub hpoly
  have hlower :
      ∀ᶠ n : ℕ in atTop,
        Real.logb 2 ((N n).choose (K n) : ℝ) / (n : ℝ) -
            Real.logb 2 ((N n + 1 : ℕ) : ℝ) / (n : ℝ) ≤
          Real.logb 2
            (MetricCodes.booleanHarmonicDimension (N n) (K n) : ℝ) /
              (n : ℝ) := by
    filter_upwards [hhalf, eventually_gt_atTop (0 : ℕ)]
      with n hhalf' hn
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hfibre :
        0 < (MetricCodes.booleanHarmonicDimension (N n) (K n) : ℝ) := by
      exact_mod_cast MetricCodes.Johnson.booleanHarmonicDimension_pos hhalf'
    have hchoosepos : 0 < ((N n).choose (K n) : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega : K n ≤ N n)
    have hlog :
        Real.logb 2 ((N n).choose (K n) : ℝ) ≤
          Real.logb 2 ((N n + 1 : ℕ) : ℝ) +
            Real.logb 2
              (MetricCodes.booleanHarmonicDimension (N n) (K n) : ℝ) := by
      rw [← Real.logb_mul (by positivity) hfibre.ne']
      apply Real.logb_le_logb_of_le
        (by norm_num : (1 : ℝ) < 2) hchoosepos
      have hcomparison :=
        MetricCodes.Hamming.choose_le_mul_hammingFibreDimension hhalf'
      change
        ((N n).choose (K n) : ℝ) ≤
          ((N n + 1 : ℕ) : ℝ) *
            (MetricCodes.booleanHarmonicDimension (N n) (K n) : ℝ)
      exact_mod_cast hcomparison
    calc
      Real.logb 2 ((N n).choose (K n) : ℝ) / (n : ℝ) -
          Real.logb 2 ((N n + 1 : ℕ) : ℝ) / (n : ℝ) =
        (Real.logb 2 ((N n).choose (K n) : ℝ) -
          Real.logb 2 ((N n + 1 : ℕ) : ℝ)) / (n : ℝ) := by ring
      _ ≤ Real.logb 2
            (MetricCodes.booleanHarmonicDimension (N n) (K n) : ℝ) /
              (n : ℝ) := by
        apply (div_le_div_iff_of_pos_right hnreal).mpr
        linarith
  have hupper :
      ∀ᶠ n : ℕ in atTop,
        Real.logb 2
            (MetricCodes.booleanHarmonicDimension (N n) (K n) : ℝ) /
              (n : ℝ) ≤
          Real.logb 2 ((N n).choose (K n) : ℝ) / (n : ℝ) := by
    filter_upwards [hhalf, eventually_gt_atTop (0 : ℕ)]
      with n hhalf' hn
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hfibre :
        0 < (MetricCodes.booleanHarmonicDimension (N n) (K n) : ℝ) := by
      exact_mod_cast MetricCodes.Johnson.booleanHarmonicDimension_pos hhalf'
    apply (div_le_div_iff_of_pos_right hnreal).mpr
    apply Real.logb_le_logb_of_le
      (by norm_num : (1 : ℝ) < 2) hfibre
    have hcomparison :=
      MetricCodes.Hamming.hammingFibreDimension_le_choose (N n) (K n)
    exact_mod_cast hcomparison
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlowerlimit hchoose hlower hupper
end MetricCodes.Johnson.Asymptotics
