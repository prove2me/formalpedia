-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.isCompact_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:07:22.622629+00:00
-- url     : https://prove2.me/submissions/d5dc1fcd-2f6a-4046-b200-064c4dae966b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyConstantCompact
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_isClosed_support_of_isLocallyConstant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Topology
variable {X : Type*} [TopologicalSpace X]
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution {f : X → ℂ} (hf : f ∈ locallyConstantCompactSupport X ℂ ℂ) :
    IsCompact (Function.support f) :=
  hf.2.of_isClosed_subset (isClosed_support_of_isLocallyConstant hf.1) (subset_tsupport f)
end GroundTheory.Automorphic.Whittaker
