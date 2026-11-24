-- Prove2me | solution 1 for GlobalTheory.Mem.Chr.Model.infIdele_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:55:42.452676+00:00
-- url     : https://prove2.me/submissions/0de71dd2-df80-43f7-8e88-d3a5942ba8ca

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
theorem _root_.solution (w : InfinitePlace L) (x : (w.Completion)ˣ) :
    ((infIdele L w x : Ideles L) : AdeleRing (𝓞 L) L).2 = 1 := rfl
end GlobalTheory.Mem.Chr.Model
