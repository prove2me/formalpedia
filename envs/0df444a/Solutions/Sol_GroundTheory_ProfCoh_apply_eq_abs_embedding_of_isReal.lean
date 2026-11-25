-- Prove2me | solution 1 for GroundTheory.ProfCoh.apply_eq_abs_embedding_of_isReal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:23:21.57598+00:00
-- url     : https://prove2.me/submissions/1281e297-f5a2-4f7c-a0e8-40542b1ffa5a

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalClassFormation_ExtensionEmbeddingOfIsRealAlgebraMap

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
open NumberField NumberField.InfinitePlace
variable {K : Type*} [Field K] [NumberField K]
omit [NumberField K]
namespace GroundTheory.ProfCoh
theorem _root_.solution {v : InfinitePlace K} (hv : v.IsReal) (x : K) :
    v x = |embedding_of_isReal hv x| := by
  rw [← norm_embedding_of_isReal hv x, Real.norm_eq_abs]
end GroundTheory.ProfCoh
