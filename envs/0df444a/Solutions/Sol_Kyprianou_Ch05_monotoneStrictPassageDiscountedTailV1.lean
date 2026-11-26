-- Prove2me | solution 1 for Kyprianou.Ch05.monotoneStrictPassageDiscountedTailV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:56:40.23361+00:00
-- url     : https://prove2.me/submissions/f5525645-76a5-4583-a5fd-17540ea5d2f4

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_monotoneStrictPassageClockBoundsV1
import Theorems.Thm_AvramDividend_Classical_positiveLIntegral_exp_neg_mul_Ioi
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_TailRatioClassL
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Set Topology Kyprianou.Ch05
open scoped Classical Topology
theorem solution
    (f : NNReal → ℝ) (hm : Monotone f) (x : ℝ) (hx : 0 ≤ x) (hz : f 0 = 0)
    (T : ENNReal)
    (hT : T = sInf ((fun t : NNReal => (t : ENNReal)) '' {t : NNReal | 0 < t ∧ x < f t}))
    (eta : ℝ) (heta : 0 < eta) :
    (∫⁻ t in Ici (0 : ℝ), if x < f t.toNNReal then
        ENNReal.ofReal (Real.exp (-eta*t)) else 0 ∂volume) =
      if T ≠ ⊤ then ENNReal.ofReal (Real.exp (-eta*T.toReal)/eta) else 0 := by
  classical
  by_cases htop : T = ⊤
  · rw [if_neg (not_not.mpr htop)]
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    apply if_neg
    intro hp
    have hpos : 0 < t.toNNReal := by
      by_contra! hh
      have he : t.toNNReal = 0 := le_antisymm hh bot_le
      rw [he,hz] at hp
      exact (not_lt_of_ge hx) hp
    have hb := (monotoneStrictPassageClockBoundsV1 f hm x T hT t.toNNReal).2 hpos hp
    rw [htop] at hb
    exact ENNReal.coe_ne_top (top_le_iff.mp hb)
  · rw [if_pos htop,← AvramDividend.Classical.positiveLIntegral_exp_neg_mul_Ioi eta T.toReal heta]
    have hsub : Ioi T.toReal ⊆ Ici (0 : ℝ) :=
      fun t ht => ENNReal.toReal_nonneg.trans (le_of_lt ht)
    rw [← Measure.restrict_restrict_of_subset hsub,← lintegral_indicator measurableSet_Ioi]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ici,
      ae_restrict_of_ae (volume.ae_ne T.toReal)] with t ht hne
    have ht' : 0 ≤ t := ht
    have hcoe : ((t.toNNReal : ENNReal)).toReal = t := by
      rw [ENNReal.coe_toReal,Real.coe_toNNReal _ ht']
    have hiff : x < f t.toNNReal ↔ T.toReal < t := by
      constructor
      · intro hp
        have hpos : 0 < t.toNNReal := by
          by_contra! hh
          have he : t.toNNReal = 0 := le_antisymm hh bot_le
          rw [he,hz] at hp
          exact (not_lt_of_ge hx) hp
        have hb := (monotoneStrictPassageClockBoundsV1 f hm x T hT t.toNNReal).2 hpos hp
        have hle := ENNReal.toReal_mono ENNReal.coe_ne_top hb
        rw [hcoe] at hle
        exact lt_of_le_of_ne hle (Ne.symm hne)
      · intro hp
        apply (monotoneStrictPassageClockBoundsV1 f hm x T hT t.toNNReal).1
        apply (ENNReal.toReal_lt_toReal htop ENNReal.coe_ne_top).mp
        rwa [hcoe]
    simp only [Set.indicator_apply,mem_Ioi,hiff]
