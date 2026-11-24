-- Prove2me | solution 1 for GlobalTheory.Mem.Chr.valued_algebraMap_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:55:43.312095+00:00
-- url     : https://prove2.me/submissions/dbbad477-ede1-464f-8a8c-af4e003036fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ValuedAlgebraMapEqOne

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
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Chr
variable (L : Type) [Field L] [NumberField L]
namespace GlobalTheory.Mem.Chr
theorem _root_.solution (v : HeightOneSpectrum (𝓞 L)) (x : 𝓞 L) (hx : x ∉ v.asIdeal) :
    Valued.v (algebraMap L (v.adicCompletion L) (algebraMap (𝓞 L) L x)) = 1 := by
  show Valued.v ((algebraMap (𝓞 L) L x : L) : v.adicCompletion L) = _
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
  exact (HeightOneSpectrum.intValuation_eq_one_iff).mpr hx
end GlobalTheory.Mem.Chr
