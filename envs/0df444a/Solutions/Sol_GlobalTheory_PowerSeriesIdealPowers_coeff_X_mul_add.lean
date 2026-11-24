-- Prove2me | solution 1 for GlobalTheory.PowerSeriesIdealPowers.coeff_X_mul_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:29:32.775416+00:00
-- url     : https://prove2.me/submissions/5f3b77d8-8baf-4bb2-8388-e0dbbf1911bd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MemPowOfCoeffMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PowerSeriesIdealPowers
open MvPowerSeries IsLocalRing
variable {O : Type} [CommRing O] [IsLocalRing O]
namespace GlobalTheory.PowerSeriesIdealPowers
theorem _root_.solution {σ : Type} [DecidableEq σ] (i : σ) (g : MvPowerSeries σ O) (d : σ →₀ ℕ) :
    coeff (d + Finsupp.single i 1) (X i * g) = coeff d g := by
  rw [X, coeff_monomial_mul]
  simp
end GlobalTheory.PowerSeriesIdealPowers
