-- Prove2me | solution 1 for GlobalTheory.FiltrationMultiplicative.coeff_part
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:56:06.257499+00:00
-- url     : https://prove2.me/submissions/cd2eb84e-6b3c-4381-9a18-cdfbfa0c4da1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FiltLePow

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
variable {O : Type} [CommRing O] [IsLocalRing O]
open Classical
namespace GlobalTheory.FiltrationMultiplicative
theorem _root_.solution {a : ℕ} (f : MvPowerSeries (Fin a) O) (i : Fin a) (q : Fin a →₀ ℕ) :
    coeff q (part f i) =
      if IsFirst (q + Finsupp.single i 1) i then coeff (q + Finsupp.single i 1) f else 0 :=
  rfl
end GlobalTheory.FiltrationMultiplicative
