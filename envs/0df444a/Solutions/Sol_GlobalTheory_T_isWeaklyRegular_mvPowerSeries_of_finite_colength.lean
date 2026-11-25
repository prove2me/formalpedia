-- Prove2me | solution 1 for GlobalTheory.T.isWeaklyRegular_mvPowerSeries_of_finite_colength
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:36:00.682274+00:00
-- url     : https://prove2.me/submissions/d9213932-ffbd-4f8b-a281-1287bd58c476

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsWeaklyRegularMvPowerSeriesOfFiniteColength
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsWeaklyRegularMvPowerSeriesOfFiniteColengthStatement
import Theorems.Thm_GlobalTheory_isWeaklyRegular_mvPowerSeries_of_pow_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] (σ : Type) [Finite σ] (n : ℕ) (e : Fin n ≃ σ) (f : σ → MvPowerSeries σ k), (∀ j, MvPowerSeries.constantCoeff (f j) = 0) → (∃ M : ℕ, Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ k)) ^ M ≤ Ideal.span (Set.range f)) → RingTheory.Sequence.IsWeaklyRegular (MvPowerSeries σ k) (List.ofFn fun i => f (e i)) := by
  first | exact @GlobalTheory.isWeaklyRegular_mvPowerSeries_of_pow_le | exact GlobalTheory.isWeaklyRegular_mvPowerSeries_of_pow_le | (intros; apply GlobalTheory.isWeaklyRegular_mvPowerSeries_of_pow_le <;> assumption)
end _root_.GlobalTheory.T
