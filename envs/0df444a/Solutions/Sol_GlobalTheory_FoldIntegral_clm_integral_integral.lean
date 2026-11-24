-- Prove2me | solution 1 for GlobalTheory.FoldIntegral.clm_integral_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:09:38.781917+00:00
-- url     : https://prove2.me/submissions/bac867db-9664-4096-afe8-44ca057bee1a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IntegralFoldViaLintegralFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.FoldIntegral
namespace GlobalTheory.FoldIntegral
theorem _root_.solution {Y Z : Type} [MeasurableSpace Y] [MeasurableSpace Z]
    (ν : Measure Y) (m : Measure Z) [SFinite m] (H : Y × Z → ℂ) (hH : Measurable H)
    (hfin : ∫⁻ y, ∫⁻ s, ‖H (y, s)‖ₑ ∂m ∂ν < ⊤) (L : ℂ →L[ℝ] ℝ) :
    L (∫ y, ∫ s, H (y, s) ∂m ∂ν) = ∫ y, ∫ s, L (H (y, s)) ∂m ∂ν := by
  have hN : Measurable fun y => ∫⁻ s, ‖H (y, s)‖ₑ ∂m := hH.enorm.lintegral_prod_right'
  have hI : Integrable (fun y => ∫ s, H (y, s) ∂m) ν :=
    ⟨hH.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable,
      lt_of_le_of_lt (lintegral_mono fun y => enorm_integral_le_lintegral_enorm _) hfin⟩
  rw [← L.integral_comp_comm hI]
  refine integral_congr_ae ?_
  filter_upwards [ae_lt_top hN hfin.ne] with y hy
  exact (L.integral_comp_comm
    ⟨(hH.comp measurable_prodMk_left).aestronglyMeasurable, hy⟩).symm
end GlobalTheory.FoldIntegral
