-- Prove2me | solution 1 for GlobalTheory.Mem.Chr.Model.localIdele_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:01:27.39916+00:00
-- url     : https://prove2.me/submissions/7a7e84ed-a207-4116-b39b-dd6def6a02a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ValuedAlgebraMapEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_DiagUnitsEqLocalIdele
import Theorems.Thm_GlobalTheory_Mem_Chr_Model_localIdele_snd_self

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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 L)) : Function.Injective (localIdele L v) := by
  intro x y hxy
  apply Units.ext
  have h := congrArg (fun z : Ideles L => (z : AdeleRing (𝓞 L) L).2 v) hxy
  simpa only [localIdele_snd_self] using h
end GlobalTheory.Mem.Chr.Model
