-- Prove2me | solution 1 for GlobalTheory.IdealPowerCoefficients.coeff_cof
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:18:17.673793+00:00
-- url     : https://prove2.me/submissions/5ed7e049-d9ea-4c5e-ae76-2c95f455d147

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MemPowIffCoeffMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.IdealPowerCoefficients
open MvPowerSeries Finsupp
variable {R : Type u_1} [CommRing R] {κ : Type u_2}
namespace GlobalTheory.IdealPowerCoefficients
theorem _root_.solution [DecidableEq κ] (f : MvPowerSeries κ R) (k : κ) (e : κ →₀ ℕ) :
    coeff e (cof f k) = if pick (e + single k 1) k = k then coeff (e + single k 1) f else 0 := by
  rw [coeff_apply]
  rfl
end GlobalTheory.IdealPowerCoefficients
