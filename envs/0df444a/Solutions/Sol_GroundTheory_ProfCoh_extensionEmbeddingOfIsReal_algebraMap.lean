-- Prove2me | solution 1 for GroundTheory.ProfCoh.extensionEmbeddingOfIsReal_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:24:50.007898+00:00
-- url     : https://prove2.me/submissions/e1296097-c631-4559-869c-08817a997982

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
    Completion.extensionEmbeddingOfIsReal hv (algebraMap K v.Completion x) = embedding_of_isReal hv x :=
  Completion.extensionEmbeddingOfIsReal_coe hv (WithAbs.toAbs v.1 x)
end GroundTheory.ProfCoh
