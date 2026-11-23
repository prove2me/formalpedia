-- Prove2me | solution 1 for GlobalTheory.PowerSeriesCoeffSum.coeff_part
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:57:06.288661+00:00
-- url     : https://prove2.me/submissions/e0380e54-81bb-4fc4-b10f-f0c6e88b8178

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_CoeffXMulPart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PowerSeriesCoeffSum
open MvPowerSeries Finsupp
variable {O : Type} [CommRing O] {a : ℕ}
namespace GlobalTheory.PowerSeriesCoeffSum
theorem _root_.solution (f : MvPowerSeries (Fin a) O) (i : Fin a) (e : Fin a →₀ ℕ) :
    coeff e (part f i) = if (∀ j < i, e j = 0) then coeff (e + single i 1) f else 0 := rfl
end GlobalTheory.PowerSeriesCoeffSum
