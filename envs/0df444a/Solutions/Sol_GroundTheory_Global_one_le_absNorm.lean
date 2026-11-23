-- Prove2me | solution 1 for GroundTheory.Global.one_le_absNorm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:29.724302+00:00
-- url     : https://prove2.me/submissions/665f08d0-b36a-49f9-9412-1a77de498d1e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Theorems.Thm_GroundTheory_Global_rationalPrimeUnder_prime
import Theorems.Thm_GroundTheory_Global_rationalPrimeUnder_le_absNorm

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
namespace GroundTheory.Global
theorem _root_.solution (w : HeightOneSpectrum (𝓞 L)) : 1 ≤ Ideal.absNorm w.asIdeal :=
  (rationalPrimeUnder_prime w).one_le.trans (rationalPrimeUnder_le_absNorm w)
end GroundTheory.Global
