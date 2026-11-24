-- Prove2me | solution 1 for GlobalTheory.FiltrationMultiplicative.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:07:16.426364+00:00
-- url     : https://prove2.me/submissions/a9d11cbf-17f4-488c-8e8d-b5f659e42c8e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FiltLePow
import Theorems.Thm_GlobalTheory_FiltrationMultiplicative_pow_le_filt
import Theorems.Thm_GlobalTheory_FiltrationMultiplicative_filt_le_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open GlobalTheory GlobalTheory.FiltrationMultiplicative
namespace GlobalTheory.FiltrationMultiplicative
theorem _root_.solution : ∀ {O : Type} [inst : CommRing O] [inst_1 : IsLocalRing O] {a : ℕ} (N : ℕ)
    (f : MvPowerSeries (Fin a) O),
    f ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) ^ N ↔
      ∀ (m : Fin a →₀ ℕ), (MvPowerSeries.coeff m : MvPowerSeries (Fin a) O → O) f ∈
        IsLocalRing.maximalIdeal O ^ (N - (Finsupp.degree : (Fin a →₀ ℕ) → ℕ) m) := by
  intro O _ _ a N f
  exact ⟨fun h => pow_le_filt N h, filt_le_pow N f⟩
end GlobalTheory.FiltrationMultiplicative
