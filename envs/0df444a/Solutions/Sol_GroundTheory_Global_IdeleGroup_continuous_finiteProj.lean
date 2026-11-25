-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.continuous_finiteProj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:07:23.382672+00:00
-- url     : https://prove2.me/submissions/5bd6dfd2-60a0-42d0-88ef-7ecd0db926fe

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe

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
open NumberField IsDedekindDomain Topology
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
variable {K}
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (finiteProj (K := K) v) :=
  Units.continuous_map ((RestrictedProduct.continuous_eval v).comp continuous_snd)
end GroundTheory.Global.IdeleGroup
