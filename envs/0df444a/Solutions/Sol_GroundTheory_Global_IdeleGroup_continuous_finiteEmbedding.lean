-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.continuous_finiteEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:07:22.753811+00:00
-- url     : https://prove2.me/submissions/40e6dd33-208d-4994-bffc-5d09e304d690

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Theorems.Thm_GroundTheory_Global_IdeleGroup_continuous_finiteAdeleSingle

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
    Continuous (finiteEmbedding (K := K) v) :=
  Units.continuous_map (continuous_const.prodMk (continuous_finiteAdeleSingle v))
end GroundTheory.Global.IdeleGroup
