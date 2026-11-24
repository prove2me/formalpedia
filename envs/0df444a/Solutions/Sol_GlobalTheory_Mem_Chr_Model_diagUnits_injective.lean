-- Prove2me | solution 1 for GlobalTheory.Mem.Chr.Model.diagUnits_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:55:39.794907+00:00
-- url     : https://prove2.me/submissions/90616df0-3f7c-48b5-9c9b-14756c3c0a8b

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
theorem _root_.solution : Function.Injective (diagUnits L) := by
  intro a b hab
  apply Units.ext
  apply NumberField.AdeleRing.algebraMap_injective (R := 𝓞 L) (K := L)
  exact congrArg (fun z : Ideles L => (z : AdeleRing (𝓞 L) L)) hab
end GlobalTheory.Mem.Chr.Model
