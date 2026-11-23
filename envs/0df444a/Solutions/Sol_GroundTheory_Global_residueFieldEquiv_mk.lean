-- Prove2me | solution 1 for GroundTheory.Global.residueFieldEquiv_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:01.451369+00:00
-- url     : https://prove2.me/submissions/c90305e2-7ea4-4f13-acd7-536d3298c68c

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalAtPlace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open GroundTheory GroundTheory.Global
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)
namespace GroundTheory.Global
theorem _root_.solution (r : R) :
    residueFieldEquiv (K := K) v (Ideal.Quotient.mk v.asIdeal r) =
      IsLocalRing.residue _ (algebraMap R (v.adicCompletionIntegers K) r) :=
  rfl
end GroundTheory.Global
