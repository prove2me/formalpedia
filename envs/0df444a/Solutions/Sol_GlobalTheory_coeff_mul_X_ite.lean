-- Prove2me | solution 1 for GlobalTheory.coeff_mul_X_ite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:31:59.155561+00:00
-- url     : https://prove2.me/submissions/80be546c-18c9-449c-accf-b1905a09ab70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MvPowerSeriesVariablesSyzygySocle

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
open MvPowerSeries Finsupp
namespace GlobalTheory
theorem _root_.solution {k : Type} [CommRing k] {g : ℕ} (f : MvPowerSeries (Fin g) k)
    (j : Fin g) (m : Fin g →₀ ℕ) :
    coeff m (f * X j) = if m j ≠ 0 then coeff (m - single j 1) f else 0 := by
  classical
  rw [X_def, coeff_mul_monomial, mul_one]
  congr 1
  simp [Finsupp.single_le_iff, Nat.one_le_iff_ne_zero]
end GlobalTheory
