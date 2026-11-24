-- Prove2me | solution 1 for GroundTheory.ProfCoh.valuation_algebraMap_of_isUnramifiedAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:49:47.177288+00:00
-- url     : https://prove2.me/submissions/ceaa92a3-d02f-4fdd-bc71-910f8ad1a78f

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_ValuationTransport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Pointwise
variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
namespace GroundTheory.ProfCoh
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K))
    (W : HeightOneSpectrum (𝓞 L)) [W.asIdeal.LiesOver w.asIdeal]
    [Algebra.IsUnramifiedAt (𝓞 K) W.asIdeal] (x : K) :
    W.valuation L (algebraMap K L x) = w.valuation K x := by
  rw [← valuation_liesOver L w W x,
    Ideal.ramificationIdx'_eq_ramificationIdx' w.asIdeal W.asIdeal
      (Ideal.map_ne_bot_of_ne_bot w.ne_bot),
    Ideal.ramificationIdx_eq_one, pow_one]
end GroundTheory.ProfCoh
