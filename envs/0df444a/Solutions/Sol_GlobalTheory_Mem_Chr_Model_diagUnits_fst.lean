-- Prove2me | solution 1 for GlobalTheory.Mem.Chr.Model.diagUnits_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:55:38.978061+00:00
-- url     : https://prove2.me/submissions/a8a96025-4693-4a03-8d2e-37873c976687

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ValuedAlgebraMapEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_DiagUnitsEqLocalIdele

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Chr.Model
variable (L : Type) [Field L] [NumberField L]
namespace GlobalTheory.Mem.Chr.Model
theorem _root_.solution (w : InfinitePlace L) (a : Lˣ) :
    ((diagUnits L a : Ideles L) : AdeleRing (𝓞 L) L).1 w = algebraMap L w.Completion a := rfl
end GlobalTheory.Mem.Chr.Model
