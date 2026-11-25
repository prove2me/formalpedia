-- Prove2me | solution 1 for GlobalTheory.NB.valTop_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:07:00.22209+00:00
-- url     : https://prove2.me/submissions/eafa05bc-19f7-4284-a8d5-0a00b91785b5

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
theorem _root_.solution (l : ℕ) {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    valTop l (0 : O) = ⊤ := if_pos rfl
end GlobalTheory.NB
