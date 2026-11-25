-- Prove2me | solution 1 for GlobalTheory.NB.valTop_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:06:56.717815+00:00
-- url     : https://prove2.me/submissions/63584a17-3559-4667-a0cc-3ba5080c865b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MapCSmulMulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open GlobalTheory GlobalTheory.NB
attribute [instance] Fr.eeRing Fr.eeAlgA Fr.eeAlgO Fr.eeTow
namespace GlobalTheory.NB
theorem _root_.solution (l : ℕ) {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {c : O} (hc : c ≠ 0) : valTop l c = (val l c : ℝ) := if_neg hc
end GlobalTheory.NB
