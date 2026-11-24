-- Prove2me | solution 1 for GlobalTheory.NormUnits.norm_eq_of_norm_sub_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:14:38.015104+00:00
-- url     : https://prove2.me/submissions/bfa28961-c958-41a0-b453-2e7552adab18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TotalDegreeCMulXMulX
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMulStarEqOfNormOneUnramifiedQuadratic
import Theorems.Thm_P2M_GlobalTheory_NormUnits_norm_sub_le_max__752f971280ab

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
open GlobalTheory GlobalTheory.NormUnits
namespace GlobalTheory.NormUnits
theorem _root_.solution {K : Type} [NormedField K] [IsUltrametricDist K] {x y : K} (h : ‖x - y‖ < ‖y‖) :
    ‖x‖ = ‖y‖ := by
  apply le_antisymm
  · calc ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ max ‖x - y‖ ‖y‖ := IsUltrametricDist.norm_add_le_max _ _
      _ = ‖y‖ := max_eq_right h.le
  · by_contra hlt
    push_neg at hlt
    have : ‖y‖ ≤ max ‖x‖ ‖x - y‖ := by
      calc ‖y‖ = ‖x - (x - y)‖ := by rw [sub_sub_cancel]
        _ ≤ max ‖x‖ ‖x - y‖ := norm_sub_le_max' _ _
    rcases le_max_iff.1 this with h1 | h1 <;> linarith
end GlobalTheory.NormUnits
