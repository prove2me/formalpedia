-- Prove2me | solution 1 for OAI.CubicTorus.profile_upper_support_slope_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T18:42:17.856841+00:00
-- url     : https://prove2.me/submissions/0e401b8d-88d5-421a-bf36-725fe1149398

import Mathlib
import Definitions.Def_OAIQ079A000
import Theorems.Thm_OAI_CubicTorus_monotoneOn_isoperimetricProfile_half

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_TubeCalibration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem profile_upper_support_slope_nonneg_oai {V : ℝ} (hV : V∈Ioo 0 (1/2))
    {C : ℝ → ℝ} (hs : Reduction.UpperSupport isoperimetricProfile C V) :
    0≤deriv C V := by
  have hd := (hs.smooth.differentiableAt (by norm_num)).hasDerivAt
  have ht := (hasDerivAt_iff_tendsto_slope_left_right.mp hd).2
  apply ge_of_tendsto ht
  have hh : Iio (1/2 : ℝ)∈𝓝 V := Iio_mem_nhds hV.2
  filter_upwards [hs.above.filter_mono nhdsWithin_le_nhds,
    Filter.Eventually.filter_mono nhdsWithin_le_nhds hh,self_mem_nhdsWithin] with W hW hWh hWV
  have he := (monotoneOn_isoperimetricProfile_half
    ⟨hV.1.le,hV.2.le⟩ ⟨hV.1.le.trans hWV.le,hWh.le⟩ hWV.le).trans hW
  rw [slope_def_field]
  exact div_nonneg (sub_nonneg.mpr (hs.contact ▸ he)) (sub_nonneg.mpr hWV.le)

end CubicTorus

end
end

end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.profile_upper_support_slope_nonneg_oai := @OAI.CubicTorus.profile_upper_support_slope_nonneg_oai
