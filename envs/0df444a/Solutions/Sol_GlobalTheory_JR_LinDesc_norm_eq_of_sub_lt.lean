-- Prove2me | solution 1 for GlobalTheory.JR.LinDesc.norm_eq_of_sub_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:01:21.49037+00:00
-- url     : https://prove2.me/submissions/7087677f-8e70-4644-83a1-898236c766f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantCompactSupportJacquetRallisDesc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.LinDesc
namespace GlobalTheory.JR.LinDesc
theorem _root_.solution {F : Type} [NormedField F] [IsUltrametricDist F] {x y : F}
    (h : ‖x - y‖ < ‖y‖) : ‖x‖ = ‖y‖ := by
  have h1 : ‖x‖ ≤ max ‖x - y‖ ‖y‖ := by
    simpa using IsUltrametricDist.norm_add_le_max (x - y) y
  have h2 : ‖y‖ ≤ max ‖y - x‖ ‖x‖ := by
    simpa using IsUltrametricDist.norm_add_le_max (y - x) x
  rw [norm_sub_rev] at h2
  rcases le_total ‖x - y‖ ‖y‖ with h3 | h3
  · rw [max_eq_right h3] at h1
    rcases le_total ‖x - y‖ ‖x‖ with h4 | h4
    · rw [max_eq_right h4] at h2; exact le_antisymm h1 h2
    · rw [max_eq_left h4] at h2; exact absurd h (not_lt.mpr h2)
  · exact absurd h (not_lt.mpr h3)
end GlobalTheory.JR.LinDesc
