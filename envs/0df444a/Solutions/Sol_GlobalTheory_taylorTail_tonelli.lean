-- Prove2me | solution 1 for GlobalTheory.taylorTail_tonelli
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:44:32.13797+00:00
-- url     : https://prove2.me/submissions/169dd796-522a-43fd-8e7e-5555cb790b64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormLeLintegralTaylorTailIteratedDeriv
import Theorems.Thm_GlobalTheory_taylorTail_inner

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set Module
open scoped ENNReal
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (f : ℝ → ℝ≥0∞) (hf : Measurable f) (j : ℕ) :
    ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ j / (j.factorial : ℝ)) * ∫⁻ s in Ioi t, f s
      = ∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal (s ^ (j+1) / ((j+1).factorial : ℝ)) * f s := by
  set w : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (t ^ j / (j.factorial : ℝ)) with hw
  have hwm : Measurable w := by fun_prop
  let G : ℝ → ℝ → ℝ≥0∞ := fun t s => w t * (Ioi t).indicator f s
  have hG : Measurable (Function.uncurry G) := by
    have hS : MeasurableSet {p : ℝ × ℝ | p.1 < p.2} := measurableSet_lt measurable_fst measurable_snd
    have : Function.uncurry G = fun p : ℝ × ℝ => w p.1 * ({p : ℝ × ℝ | p.1 < p.2}.indicator (fun p => f p.2) p) := by
      ext ⟨t, s⟩
      simp only [Function.uncurry_apply_pair, G, Set.indicator, mem_Ioi, mem_setOf_eq]
    rw [this]
    exact (hwm.comp measurable_fst).mul ((hf.comp measurable_snd).indicator hS)
  have step1 : ∫⁻ t in Ioi (0:ℝ), w t * ∫⁻ s in Ioi t, f s
      = ∫⁻ t in Ioi (0:ℝ), ∫⁻ s in Ioi (0:ℝ), G t s := by
    refine setLIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    simp only [G]
    rw [lintegral_const_mul _ (hf.indicator measurableSet_Ioi), lintegral_indicator measurableSet_Ioi,
      Measure.restrict_restrict measurableSet_Ioi, Ioi_inter_Ioi, sup_eq_left.mpr (le_of_lt (mem_Ioi.mp ht))]
  rw [step1, lintegral_lintegral_swap hG.aemeasurable]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
  have : ∀ t, G t s = (Iio s).indicator w t * f s := by
    intro t
    by_cases h : t < s <;> simp [G, Set.indicator, h]
  simp_rw [this]
  rw [lintegral_mul_const _ (hwm.indicator measurableSet_Iio), lintegral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio, Iio_inter_Ioi, taylorTail_inner j s hs]
end GlobalTheory
