-- Prove2me | solution 1 for GroundTheory.PAdicHodge.KSubset.range_emb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:26:40.183543+00:00
-- url     : https://prove2.me/submissions/8d280af7-810c-4625-a306-cc2899d5e89e

import Mathlib
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_ExistsMaxMinorNeZeroOfLinearIndependentAlt
import Definitions.Def_GroundTheory_PAdicHodge_SlopeCauchyBinet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Matrix Finset Equiv
namespace GroundTheory.PAdicHodge
namespace KSubset
theorem _root_.solution {n k : ℕ} (s : KSubset n k) : Set.range s.emb = (s.1 : Set (Fin n)) :=
  Finset.range_orderEmbOfFin _ _
end KSubset
end GroundTheory.PAdicHodge
