-- Prove2me | solution 1 for GlobalTheory.Mem.Chr.Model.diagUnits_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:04:29.319538+00:00
-- url     : https://prove2.me/submissions/f7bb8677-154e-4585-8061-717a39f48804

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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 L)) (a : Lˣ) :
    ((diagUnits L a : Ideles L) : AdeleRing (𝓞 L) L).2 v = algebraMap L (v.adicCompletion L) a := rfl
end GlobalTheory.Mem.Chr.Model
