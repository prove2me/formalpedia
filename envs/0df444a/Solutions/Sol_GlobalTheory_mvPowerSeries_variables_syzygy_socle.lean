-- Prove2me | solution 1 for GlobalTheory.mvPowerSeries_variables_syzygy_socle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:31:16.632865+00:00
-- url     : https://prove2.me/submissions/4b50c847-922e-4157-bf70-d45d4c82c713

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MvPowerSeriesVariablesSyzygySocle
import Theorems.Thm_GlobalTheory_mvPowerSeries_X_syzygy
import Theorems.Thm_GlobalTheory_mvPowerSeries_prod_X_pow_notMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (k : Type) [Field k] (g : ℕ) (x : Fin g → MvPowerSeries (Fin g) k), (∀ i, x i = MvPowerSeries.X i) → (∀ r : Fin g → _, ∑ i, r i * x i = 0 → ∃ s : Matrix (Fin g) (Fin g) _, s.transpose = -s ∧ (∀ i, s i i = 0) ∧ r = s.mulVec x) ∧ ∀ N : ℕ, ∏ i, x i ^ N ∉ Ideal.span (Set.range fun i => x i ^ (N + 1)) := by
  intro k _ g x hx
  obtain rfl : x = fun i => MvPowerSeries.X i := funext hx
  exact ⟨fun r hr => mvPowerSeries_X_syzygy r hr, fun N => mvPowerSeries_prod_X_pow_notMem N⟩
end GlobalTheory
