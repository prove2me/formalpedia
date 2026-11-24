-- Prove2me | solution 1 for GlobalTheory.PowerSeriesShift.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:47:43.67583+00:00
-- url     : https://prove2.me/submissions/3469b923-f3d8-4000-9b96-9803e47d142b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqXMulShiftAdd
import Theorems.Thm_GlobalTheory_PowerSeriesShift_eq_X_mul_shift_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PowerSeriesShift
namespace GlobalTheory.PowerSeriesShift
theorem _root_.solution : (let d1 : {σ O : Type} → [CommRing O] → σ → MvPowerSeries σ O → MvPowerSeries σ O := @(fun {σ O : Type} [CommRing O] (i : σ) (f : MvPowerSeries σ O) (m : σ →₀ ℕ) ↦ (MvPowerSeries.coeff ((fun₀ | i => (1 : ℕ)) + m) : MvPowerSeries σ O → O) f); let d2 : {σ O : Type} → [CommRing O] → σ → MvPowerSeries σ O → MvPowerSeries σ O := @(fun {σ O : Type} [CommRing O] (i : σ) (f : MvPowerSeries σ O) (m : σ →₀ ℕ) ↦ if (m : σ → ℕ) i = (0 : ℕ) then (MvPowerSeries.coeff m : MvPowerSeries σ O → O) f else (0 : O)); ∀ {σ O : Type} [inst : CommRing O] (i : σ) (f : MvPowerSeries σ O), f = MvPowerSeries.X i * d1 i f + d2 i f) := by
  intro d1 d2 σ O _ i f
  exact eq_X_mul_shift_add i f
end GlobalTheory.PowerSeriesShift
