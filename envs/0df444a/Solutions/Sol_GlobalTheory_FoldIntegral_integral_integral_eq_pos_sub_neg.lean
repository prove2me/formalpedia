-- Prove2me | solution 1 for GlobalTheory.FoldIntegral.integral_integral_eq_pos_sub_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:09:39.639797+00:00
-- url     : https://prove2.me/submissions/de43f67a-9230-4561-8e59-a80b621386d5

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
    (ν : Measure Y) (m : Measure Z) [SFinite m] (h : Y × Z → ℝ) (hh : Measurable h)
    (hfin : ∫⁻ y, ∫⁻ s, ‖h (y, s)‖ₑ ∂m ∂ν < ⊤) :
    ∫ y, ∫ s, h (y, s) ∂m ∂ν =
      (∫⁻ y, ∫⁻ s, ENNReal.ofReal (h (y, s)) ∂m ∂ν).toReal -
        (∫⁻ y, ∫⁻ s, ENNReal.ofReal (-h (y, s)) ∂m ∂ν).toReal := by
  have hN : Measurable fun y => ∫⁻ s, ‖h (y, s)‖ₑ ∂m := hh.enorm.lintegral_prod_right'
  have hp : Measurable fun y => ∫⁻ s, ENNReal.ofReal (h (y, s)) ∂m :=
    hh.ennreal_ofReal.lintegral_prod_right'
  have hn : Measurable fun y => ∫⁻ s, ENNReal.ofReal (-h (y, s)) ∂m :=
    hh.neg.ennreal_ofReal.lintegral_prod_right'
  have bp : ∫⁻ y, ∫⁻ s, ENNReal.ofReal (h (y, s)) ∂m ∂ν < ⊤ :=
    lt_of_le_of_lt (lintegral_mono fun y => lintegral_mono fun s => Real.ofReal_le_enorm _) hfin
  have bn : ∫⁻ y, ∫⁻ s, ENNReal.ofReal (-h (y, s)) ∂m ∂ν < ⊤ :=
    lt_of_le_of_lt (lintegral_mono fun y => lintegral_mono fun s =>
      (Real.ofReal_le_enorm _).trans (enorm_neg _).le) hfin
  rw [← integral_toReal hp.aemeasurable (ae_lt_top hp bp.ne),
    ← integral_toReal hn.aemeasurable (ae_lt_top hn bn.ne),
    ← integral_sub (integrable_toReal_of_lintegral_ne_top hp.aemeasurable bp.ne)
      (integrable_toReal_of_lintegral_ne_top hn.aemeasurable bn.ne)]
  refine integral_congr_ae ?_
  filter_upwards [ae_lt_top hN hfin.ne] with y hy
  exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part
    ⟨(hh.comp measurable_prodMk_left).aestronglyMeasurable, hy⟩
end GlobalTheory.FoldIntegral
