-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.frobeniusClosure_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:14:52.128797+00:00
-- url     : https://prove2.me/submissions/dba30c33-1df8-4686-9374-dd313e569873

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Frobenius

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
open ProfiniteInteger
variable {G : Type*} [Group G] {d : G →* Multiplicative ℤ̂} {L : Subgroup G} {σ : G}
variable [TopologicalSpace G] [IsTopologicalGroup G]
namespace GroundTheory.LocalField.Abstract
theorem _root_.solution {K : Subgroup G} (hK : IsClosed (K : Set G)) (hσK : σ ∈ K)
    (hLK : L ⊓ d.ker ≤ K) : frobeniusClosure d L σ ≤ K :=
  Subgroup.topologicalClosure_minimal _ (sup_le (Subgroup.zpowers_le.2 hσK) hLK) hK
end GroundTheory.LocalField.Abstract
