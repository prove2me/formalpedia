-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Bridge.absOfVal_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:51:54.216428+00:00
-- url     : https://prove2.me/submissions/f6259bb7-7211-4507-80f0-ee6a394b956e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LocallyCompactOfComplete
import Theorems.Thm_GlobalTheory_UnitLemma_Bridge_absOfVal_le_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Bridge
namespace GlobalTheory.UnitLemma.Bridge
theorem _root_.solution {E : Type} [Field E] (v : Valuation E (WithZero (Multiplicative ℤ))) {x y : E}
    (h : v x = v y) : absOfVal v x = absOfVal v y :=
  le_antisymm ((absOfVal_le_iff v _ _).2 h.le) ((absOfVal_le_iff v _ _).2 h.ge)
end GlobalTheory.UnitLemma.Bridge
