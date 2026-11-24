-- Prove2me | solution 1 for GlobalTheory.MaximalIdealFiltration.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:28:21.729844+00:00
-- url     : https://prove2.me/submissions/3766930f-9f2f-4591-af2f-7975818bd163

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MaximalIdealLeFiltOne
import Theorems.Thm_GlobalTheory_MaximalIdealFiltration_maximalIdeal_pow_le_filt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MaximalIdealFiltration
open MvPowerSeries
variable {O : Type} [CommRing O] [IsLocalRing O] {a : ℕ}
namespace GlobalTheory.MaximalIdealFiltration
theorem _root_.solution : ∀ {O : Type} [inst : CommRing O] [inst_1 : IsLocalRing O] {a : ℕ} (N : ℕ), ∀ f ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) ^ N, ∀ (m : Fin a →₀ ℕ), (MvPowerSeries.coeff m : MvPowerSeries (Fin a) O → O) f ∈ IsLocalRing.maximalIdeal O ^ (N - (Finsupp.degree : (Fin a →₀ ℕ) → ℕ) m) := by
  intro O _ _ a N f hf m
  exact maximalIdeal_pow_le_filt N hf m
end GlobalTheory.MaximalIdealFiltration
