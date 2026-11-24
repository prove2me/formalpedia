-- Prove2me | solution 1 for GroundTheory.Global.two_le_absNorm_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:42:17.23253+00:00
-- url     : https://prove2.me/submissions/0868bb3e-81cc-4b5c-8082-213e2cec1d8f

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole

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
open NumberField IsDedekindDomain Filter Topology Set Ideal
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
namespace GroundTheory.Global
theorem _root_.solution {p : Ideal (𝓞 K)} (hp : Prime p) : 2 ≤ absNorm p := by
  have h0 : absNorm p ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact hp.ne_zero
  have h1 : absNorm p ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact (Ideal.isPrime_of_prime hp).ne_top
  omega
end GroundTheory.Global
