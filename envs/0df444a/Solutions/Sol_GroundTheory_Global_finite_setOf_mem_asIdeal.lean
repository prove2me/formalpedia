-- Prove2me | solution 1 for GroundTheory.Global.finite_setOf_mem_asIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:08:43.986529+00:00
-- url     : https://prove2.me/submissions/549eedad-6d0f-4b44-9107-bfb81ad088ef

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_PrimeLocalization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain Polynomial
noncomputable section
variable (L : Type*) [Field L] [NumberField L]
variable {L}
namespace GroundTheory.Global
theorem _root_.solution {b : 𝓞 L} (hb : b ≠ 0) :
    {v : HeightOneSpectrum (𝓞 L) | b ∈ v.asIdeal}.Finite :=
  (Ideal.finite_factors (I := Ideal.span {b}) (by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot])).subset
    fun _ hv => Ideal.dvd_span_singleton.mpr hv
end GroundTheory.Global
