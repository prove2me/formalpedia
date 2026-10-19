-- Prove2me | solution 1 for MetricCodes.Spherical.GeneralSpectral.eventually_transverse_add_le_longitudinal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.020426+00:00
-- url     : https://prove2.me/submissions/010870de-207a-484b-b25e-ea7a460d3bc2

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_tendsto_longitudinal_ratio
import Theorems.Thm_MetricCodes_Hamming_tendsto_transverse_ratio
import Theorems.Thm_MetricCodes_Spherical_GeneralSpectral_tendsto_longitudinal_ratio
import Theorems.Thm_MetricCodes_Spherical_GeneralSpectral_tendsto_transverse_ratio

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
theorem _root_.solution
    {a b : ℝ} (hb : 0 ≤ b) (hba : b < a) (m : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      transverseDegree b n + m ≤ longitudinalDegree a n := by
  have ha : 0 < a := lt_of_le_of_lt hb hba
  let δ : ℝ := (a - b) / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  have hδlt : δ < a - b := by
    dsimp [δ]
    linarith
  have hratio :=
    ((tendsto_longitudinal_ratio ha.le).sub
      (tendsto_transverse_ratio hb)).eventually
        (lt_mem_nhds hδlt)
  have hgrowth :
      Tendsto (fun n : ℕ => δ * (n : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop hδ
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlarge := hgrowth.eventually
    (eventually_ge_atTop (m : ℝ))
  filter_upwards [hratio, hlarge, eventually_gt_atTop (0 : ℕ)]
    with n hnratio hnlarge hn
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hmul := mul_lt_mul_of_pos_right hnratio hnreal
  have hidentity :
      (((longitudinalDegree a n : ℝ) / (n : ℝ) -
        (transverseDegree b n : ℝ) / (n : ℝ)) * (n : ℝ)) =
        (longitudinalDegree a n : ℝ) -
          (transverseDegree b n : ℝ) := by
    field_simp [ne_of_gt hnreal]
  rw [hidentity] at hmul
  have hreal :
      (transverseDegree b n : ℝ) + (m : ℝ) ≤
        (longitudinalDegree a n : ℝ) := by
    linarith
  exact_mod_cast hreal
end MetricCodes.Spherical.GeneralSpectral
