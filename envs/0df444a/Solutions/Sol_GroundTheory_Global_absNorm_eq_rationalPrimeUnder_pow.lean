-- Prove2me | solution 1 for GroundTheory.Global.absNorm_eq_rationalPrimeUnder_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:57:07.832032+00:00
-- url     : https://prove2.me/submissions/32944bb3-d238-41a7-8c97-3386753f78d0

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
namespace GroundTheory.Global
theorem _root_.solution (w : HeightOneSpectrum (𝓞 L)) :
    Ideal.absNorm w.asIdeal = rationalPrimeUnder w ^ w.asIdeal.inertiaDeg ℤ :=
  (Ideal.absNorm_pow_inertiaDeg (w.asIdeal.under ℤ) w.asIdeal).symm
end GroundTheory.Global
