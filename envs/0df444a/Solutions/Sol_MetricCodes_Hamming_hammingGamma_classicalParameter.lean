-- Prove2me | solution 1 for MetricCodes.Hamming.hammingGamma_classicalParameter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.946406+00:00
-- url     : https://prove2.me/submissions/d9c6e49b-bf67-40e9-8e11-f16dab1da37a

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_classicalParameter_lt_half
import Theorems.Thm_MetricCodes_Hamming_classicalParameter_pos
import Theorems.Thm_MetricCodes_Hamming_classicalParameter_mul_one_sub
import Theorems.Thm_MetricCodes_Hamming_hammingGamma_zero

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
set_option autoImplicit false
open Filter Metric Topology
open scoped BigOperators InnerProductSpace Topology
open MetricCodes.Hamming
namespace MetricCodes.Hamming
theorem _root_.solution {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < (1 : ℝ) / 2) :
    MetricCodes.hammingGamma (classicalParameter δ) 0 = 1 - 2 * δ := by
  have ha := classicalParameter_pos hδ hδ'
  have ha' : classicalParameter δ < 1 :=
    (classicalParameter_lt_half hδ hδ').trans (by norm_num)
  rw [hammingGamma_zero ha ha',
    classicalParameter_mul_one_sub hδ hδ',
    Real.sqrt_sq (by linarith : 0 ≤ (1 : ℝ) / 2 - δ)]
  ring
end MetricCodes.Hamming
