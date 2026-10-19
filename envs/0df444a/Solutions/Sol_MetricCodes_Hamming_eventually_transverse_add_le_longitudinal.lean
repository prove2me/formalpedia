-- Prove2me | solution 1 for MetricCodes.Hamming.eventually_transverse_add_le_longitudinal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.946406+00:00
-- url     : https://prove2.me/submissions/4e398c7e-59f1-4565-8e60-d8a70f73173e

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_tendsto_longitudinal_ratio
import Theorems.Thm_MetricCodes_Hamming_tendsto_transverse_ratio

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
    {a b : ℝ} (hb : 0 ≤ b) (hba : b < a) (m : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      transverseDegree b n + m ≤ longitudinalDegree a n := by
  let ε : ℝ := (a - b) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  have hεlt : ε < a - b := by
    dsimp [ε]
    linarith
  have ha : 0 ≤ a := (lt_of_le_of_lt hb hba).le
  have hratio :=
    ((tendsto_longitudinal_ratio ha).sub
      (tendsto_transverse_ratio hb)).eventually
        (lt_mem_nhds hεlt)
  have hgrowth :
      Tendsto (fun n : ℕ => ε * (n : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop hε
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlarge := hgrowth.eventually (eventually_ge_atTop (m : ℝ))
  filter_upwards [hratio, hlarge, eventually_gt_atTop (0 : ℕ)]
    with n hnratio hnlarge hn
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hmul := mul_lt_mul_of_pos_right hnratio hnreal
  have hidentity :
      (((longitudinalDegree a n : ℝ) / (n : ℝ) -
        (transverseDegree b n : ℝ) / (n : ℝ)) * (n : ℝ)) =
        (longitudinalDegree a n : ℝ) -
          (transverseDegree b n : ℝ) := by
    field_simp [hnreal.ne']
  rw [hidentity] at hmul
  have hreal :
      (transverseDegree b n : ℝ) + (m : ℝ) ≤
        (longitudinalDegree a n : ℝ) := by
    linarith
  exact_mod_cast hreal
end MetricCodes.Hamming
