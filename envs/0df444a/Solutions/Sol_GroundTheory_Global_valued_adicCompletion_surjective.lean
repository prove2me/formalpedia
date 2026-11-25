-- Prove2me | solution 1 for GroundTheory.Global.valued_adicCompletion_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:09:45.695549+00:00
-- url     : https://prove2.me/submissions/670e7aff-a93b-415e-9e8f-d1c8a8029ed0

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalAtPlace
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField WithZero
open scoped WithZero
open GroundTheory GroundTheory.Global
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)
namespace GroundTheory.Global
theorem _root_.solution :
    Function.Surjective (Valued.v : v.adicCompletion K → ℤᵐ⁰) :=
  valuedAdicCompletion_surjective K v
end GroundTheory.Global
