-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Bridge.mem_fixedField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:51:59.76882+00:00
-- url     : https://prove2.me/submissions/7e98362a-3163-4590-aa68-a62509dce6f0

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
theorem _root_.solution {E : Type} [Field E] (c : E ≃+* E) (x : E) : x ∈ fixedField c ↔ c x = x := Iff.rfl
end GlobalTheory.UnitLemma.Bridge
