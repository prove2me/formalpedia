-- Prove2me | solution 1 for GroundTheory.Global.span_rationalPrimeUnder
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:09:50.6708+00:00
-- url     : https://prove2.me/submissions/30841589-bdc9-4ee0-8adb-7a886060ab2e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes

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
open NumberField IsDedekindDomain Filter Topology Set
noncomputable section
variable {K L : Type*} [Field L] [NumberField L]
omit [NumberField L]
namespace GroundTheory.Global
theorem _root_.solution (w : HeightOneSpectrum (𝓞 L)) :
    Ideal.span {((rationalPrimeUnder w : ℕ) : ℤ)} = w.asIdeal.under ℤ :=
  Int.ideal_span_absNorm_eq_self _
end GroundTheory.Global
