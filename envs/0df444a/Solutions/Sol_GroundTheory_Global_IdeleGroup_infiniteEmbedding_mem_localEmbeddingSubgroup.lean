-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.infiniteEmbedding_mem_localEmbeddingSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:45:26.91937+00:00
-- url     : https://prove2.me/submissions/a9df60cc-2186-4b85-974f-ede90d3e4ca7

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_NormResidueSymbol_Abstract
import Definitions.Def_GroundTheory_GlobalFields_NormResidueSymbol_AbstractUnique

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
open Filter Topology NumberField IsDedekindDomain
open scoped NumberField.AdeleRing
noncomputable section
open GroundTheory.Global.IdeleGroup
variable (K : Type*) [Field K] [NumberField K]
variable {K}
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution (w : InfinitePlace K) (a : (w.Completion)ˣ) :
    infiniteEmbedding w a ∈ localEmbeddingSubgroup K :=
  Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem w ⟨a, rfl⟩)
end GroundTheory.Global.IdeleGroup
