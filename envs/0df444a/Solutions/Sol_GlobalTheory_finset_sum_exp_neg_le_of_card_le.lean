-- Prove2me | solution 1 for GlobalTheory.finset_sum_exp_neg_le_of_card_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:03:04.703613+00:00
-- url     : https://prove2.me/submissions/493e9490-754e-408c-ab05-9af449a0a9b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteInterClosedBallOfSeparated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_GaussianSumOfOneSeparatedOfLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric MeasureTheory Module Set Real
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {ι : Type*} (s : Finset ι) (f : ι → ℝ) {t C : ℝ}
    (hf : ∀ i ∈ s, t ≤ f i)
    (hc : ∀ u, t ≤ u → ((s.filter fun i => f i ≤ u).card : ℝ) ≤ C * exp ((u - t) / 2)) :
    ∑ i ∈ s, exp (-f i) ≤ 2 * C * exp (-t) := by
  have hint : IntegrableOn (fun u : ℝ => exp (-u)) (Ici t) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).2 (integrableOn_exp_neg_Ioi t)
  have h1 : ∀ i ∈ s, exp (-f i) =
      ∫ u in Ici t, (Ici (f i)).indicator (fun u : ℝ => exp (-u)) u := by
    intro i hi
    rw [setIntegral_indicator measurableSet_Ici, Ici_inter_Ici, sup_eq_right.2 (hf i hi),
      integral_Ici_eq_integral_Ioi, integral_exp_neg_Ioi]
  have hint2 : IntegrableOn (fun u : ℝ => exp (-(1 / 2) * u)) (Ici t) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).2 (exp_neg_integrableOn_Ioi t (by norm_num))
  rw [Finset.sum_congr rfl h1, ← integral_finset_sum _
    (fun i _ => hint.indicator measurableSet_Ici)]
  calc ∫ u in Ici t, ∑ i ∈ s, (Ici (f i)).indicator (fun u : ℝ => exp (-u)) u
      ≤ ∫ u in Ici t, (C * exp (-t / 2)) * exp (-(1 / 2) * u) := by
        refine setIntegral_mono_on
          (integrable_finset_sum _ fun i _ => hint.indicator measurableSet_Ici)
          (hint2.const_mul _) measurableSet_Ici fun u hu => ?_
        have e : ∑ i ∈ s, (Ici (f i)).indicator (fun u : ℝ => exp (-u)) u =
            ((s.filter fun i => f i ≤ u).card : ℝ) * exp (-u) := by
          simp only [indicator, mem_Ici]
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        rw [e]
        calc _ ≤ C * exp ((u - t) / 2) * exp (-u) :=
              mul_le_mul_of_nonneg_right (hc u hu) (exp_pos _).le
          _ = _ := by
              rw [mul_assoc, mul_assoc, ← exp_add, ← exp_add]; congr 2; ring
    _ = 2 * C * exp (-t) := by
        rw [integral_const_mul, integral_Ici_eq_integral_Ioi,
          integral_exp_mul_Ioi (by norm_num)]
        have : exp (-t) = exp (-t / 2) * exp (-(1 / 2) * t) := by
          rw [← exp_add]; congr 1; ring
        rw [this]; ring
end GlobalTheory
