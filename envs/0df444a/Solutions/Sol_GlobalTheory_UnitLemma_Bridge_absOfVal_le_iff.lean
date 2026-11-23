-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Bridge.absOfVal_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:10:01.753628+00:00
-- url     : https://prove2.me/submissions/c912b6d2-6836-4893-b306-c0ac28565074

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LocallyCompactOfComplete

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
theorem _root_.solution {E : Type} [Field E] (v : Valuation E (WithZero (Multiplicative ℤ))) (x y : E) :
    absOfVal v x ≤ absOfVal v y ↔ v x ≤ v y :=
  NNReal.coe_le_coe.trans (WithZeroMulInt.toNNReal_strictMono (e := 2) one_lt_two).le_iff_le
end GlobalTheory.UnitLemma.Bridge
