-- Prove2me | solution 1 for OAI.CubicTorus.profile_upper_support_slope_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T18:43:08.238309+00:00
-- url     : https://prove2.me/submissions/f80011dd-f145-49be-8654-1030c409f973

import Mathlib
import Definitions.Def_OAIQ079A000
import Theorems.Thm_OAI_CubicTorus_antitoneOn_isoperimetricProfile_half

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

theorem profile_upper_support_slope_nonpos_oai {V : ℝ} (hV : V∈Ioo (1/2) 1)
    {C : ℝ → ℝ} (hs : Reduction.UpperSupport isoperimetricProfile C V) :
    deriv C V≤0 := by
  have hd := (hs.smooth.differentiableAt (by norm_num)).hasDerivAt
  have ht := (hasDerivAt_iff_tendsto_slope_left_right.mp hd).1
  apply le_of_tendsto ht
  have hh : Ioi (1/2 : ℝ)∈𝓝 V := Ioi_mem_nhds hV.1
  filter_upwards [hs.above.filter_mono nhdsWithin_le_nhds,
    Filter.Eventually.filter_mono nhdsWithin_le_nhds hh,self_mem_nhdsWithin] with W hW hWh hWV
  have he := (antitoneOn_isoperimetricProfile_half
    ⟨hWh.le,hWV.le.trans hV.2.le⟩ ⟨hV.1.le,hV.2.le⟩ hWV.le).trans hW
  rw [slope_def_field]
  exact div_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hs.contact ▸ he)) (sub_nonpos.mpr hWV.le)

end CubicTorus

end
end

end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.profile_upper_support_slope_nonpos_oai := @OAI.CubicTorus.profile_upper_support_slope_nonpos_oai
