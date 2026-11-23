-- Prove2me | solution 1 for GroundTheory.Global.rationalPrimeUnder_prime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:02:56.57373+00:00
-- url     : https://prove2.me/submissions/a6a4976b-e38d-419f-b317-330e3b77d0fe

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Theorems.Thm_GroundTheory_Global_under_int_ne_bot

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
theorem _root_.solution (w : HeightOneSpectrum (𝓞 L)) : (rationalPrimeUnder w).Prime :=
  (Int.prime_absNorm _).mpr (Ideal.prime_of_isPrime (under_int_ne_bot w) inferInstance)
end GroundTheory.Global
