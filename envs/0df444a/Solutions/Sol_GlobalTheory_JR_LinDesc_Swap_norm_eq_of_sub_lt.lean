-- Prove2me | solution 1 for GlobalTheory.JR.LinDesc.Swap.norm_eq_of_sub_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:01:10.122206+00:00
-- url     : https://prove2.me/submissions/60cc2a7b-81f9-438e-bd02-32b5b44824a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LinearDescentPartialFourierEqFourierDescent

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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.LinDesc GlobalTheory.JR.LinDesc.Swap
namespace GlobalTheory.JR.LinDesc.Swap
theorem _root_.solution {K : Type} [NormedField K] [IsUltrametricDist K] {x y : K}
    (h : ‖x - y‖ < ‖y‖) : ‖x‖ = ‖y‖ := by
  have h1 : ‖x‖ ≤ max ‖x - y‖ ‖y‖ := by
    simpa using IsUltrametricDist.norm_add_le_max (x - y) y
  have h2 : ‖y‖ ≤ max ‖y - x‖ ‖x‖ := by
    simpa using IsUltrametricDist.norm_add_le_max (y - x) x
  rw [norm_sub_rev] at h2
  apply le_antisymm
  · exact h1.trans (max_le h.le le_rfl)
  · rcases le_max_iff.mp h2 with h3 | h3
    · exact absurd h3 (not_le.mpr h)
    · exact h3
end GlobalTheory.JR.LinDesc.Swap
