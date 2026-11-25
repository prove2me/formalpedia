-- Prove2me | solution 1 for GroundTheory.Global.normalizedAbv_eq_toNNReal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:09:53.921751+00:00
-- url     : https://prove2.me/submissions/7663fb33-e109-43f1-8385-9e1e18290be5

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
variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
namespace GroundTheory.Global
theorem _root_.solution (x : v.adicCompletion K) :
    normalizedAbv v x = WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (Valued.v x) :=
  FinitePlace.norm_def v x
end GroundTheory.Global
