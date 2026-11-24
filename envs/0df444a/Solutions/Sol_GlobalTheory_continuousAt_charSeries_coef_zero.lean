-- Prove2me | solution 1 for GlobalTheory.continuousAt_charSeries_coef_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:33:57.018802+00:00
-- url     : https://prove2.me/submissions/637eeeca-2d9e-40dd-8cb3-12b176d3056e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousAtCharSeriesCoefZero
import Theorems.Thm_GlobalTheory_CharSeriesCoef_continuousAt_coef_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
namespace GlobalTheory
theorem _root_.solution :
    ∀ {Y Ξ P : Type} [AddCommGroup Y] [Zero Ξ] [TopologicalSpace P] (e : Ξ → AddChar Y ℂ),
    (∀ a y, ‖e a y‖ = 1) → (∀ y, e 0 y = 1) → (∀ a, a ≠ 0 → ∃ y, e a y ≠ 1) →
    ∀ (c : P → Ξ → ℂ) (p0 : P) (M : Ξ → ℝ), Summable M → (∀ᶠ p in nhds p0, ∀ a, ‖c p a‖ ≤ M a) →
    (∀ y, ContinuousAt (fun p => ∑' a, e a y * c p a) p0) → ContinuousAt (fun p => c p 0) p0 :=
  fun e hn he0 hne c p0 M hM hb hc =>
    GlobalTheory.CharSeriesCoef.continuousAt_coef_zero e hn he0 hne c p0 M hM hb hc
end GlobalTheory
