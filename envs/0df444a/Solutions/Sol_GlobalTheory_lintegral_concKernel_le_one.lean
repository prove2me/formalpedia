-- Prove2me | solution 1 for GlobalTheory.lintegral_concKernel_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:19:03.938134+00:00
-- url     : https://prove2.me/submissions/a8a38ad8-04c4-46ba-8a9f-fff65a82c75b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TendstoLintegralPoissonKernelBoundary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {t : ℝ} (ht : 0 < t) :
    ∫⁻ s in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (t / (1 - s + t) ^ 2) ≤ 1 := by
  have hpos : ∀ s ∈ Set.uIcc (0 : ℝ) 1, 1 - s + t ≠ 0 := by
    intro s hs
    rw [Set.uIcc_of_le zero_le_one] at hs
    have := hs.2
    linarith
  have hc : ContinuousOn (fun s : ℝ => t / (1 - s + t) ^ 2) (Set.uIcc (0 : ℝ) 1) :=
    ContinuousOn.div continuousOn_const (by fun_prop) (fun s hs => pow_ne_zero 2 (hpos s hs))
  have hint : ∫ s in (0 : ℝ)..1, t / (1 - s + t) ^ 2 = t / (1 - 1 + t) - t / (1 - 0 + t) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => t / (1 - s + t)) ?_
      hc.intervalIntegrable
    intro s hs
    have h1 : HasDerivAt (fun s : ℝ => 1 - s + t) (-1) s := by
      simpa using ((hasDerivAt_id s).const_sub 1).add_const t
    have h2 := (hasDerivAt_const s t).fun_div h1 (hpos s hs)
    have h3 : (0 * (1 - s + t) - t * -1) / (1 - s + t) ^ 2 = t / (1 - s + t) ^ 2 := by ring
    exact h3 ▸ h2
  rw [Set.uIcc_of_le zero_le_one] at hc
  rw [← ofReal_integral_eq_lintegral_ofReal (hc.integrableOn_compact isCompact_Icc)
    (Filter.Eventually.of_forall fun s => by positivity), integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one, hint]
  apply ENNReal.ofReal_le_one.2
  have : 0 ≤ t / (1 - 0 + t) := by positivity
  have h3 : t / (1 - 1 + t) = 1 := by
    rw [sub_self, zero_add, div_self ht.ne']
  linarith
end GlobalTheory
