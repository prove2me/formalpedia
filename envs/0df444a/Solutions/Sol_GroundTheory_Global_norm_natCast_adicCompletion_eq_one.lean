-- Prove2me | solution 1 for GroundTheory.Global.norm_natCast_adicCompletion_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:30.327175+00:00
-- url     : https://prove2.me/submissions/f3f36b55-9c99-4e03-9c31-0b217e9fc0b5

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IndexProductFormula

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
open NumberField IsDedekindDomain
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution {v : HeightOneSpectrum (𝓞 K)} {n : ℕ}
    (hv : (n : 𝓞 K) ∉ v.asIdeal) : ‖(n : v.adicCompletion K)‖ = 1 := by
  have h := (FinitePlace.norm_eq_one_iff_notMem (K := K) (v := v) (n : 𝓞 K)).2 hv
  rwa [map_natCast, map_natCast] at h
end GroundTheory.Global
