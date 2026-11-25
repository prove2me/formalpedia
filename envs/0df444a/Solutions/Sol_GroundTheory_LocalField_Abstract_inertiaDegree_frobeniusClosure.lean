-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.inertiaDegree_frobeniusClosure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:44:02.228815+00:00
-- url     : https://prove2.me/submissions/ab26548b-606a-496a-8d89-668c51899963

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Frobenius
import Theorems.Thm_GroundTheory_LocalField_Abstract_map_frobeniusClosure
import Theorems.Thm_GroundTheory_LocalField_Abstract_ProfiniteInteger_index_multiples


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
variable [CompactSpace G] [TotallyDisconnectedSpace G]
omit [TotallyDisconnectedSpace G]
namespace GroundTheory.LocalField.Abstract
theorem _root_.solution (hd : Continuous d)
    (hσ : σ ∈ Subgroup.normalizer ((L ⊓ d.ker : Subgroup G) : Set G)) {N : ℕ} (hN : N ≠ 0)
    (hdσ : d σ = Multiplicative.ofAdd (N : ℤ̂)) :
    inertiaDegree d (frobeniusClosure d L σ) = N := by
  rw [inertiaDegree, map_frobeniusClosure hd hσ hdσ, AddSubgroup.index_toSubgroup]
  exact index_multiples ⟨N, Nat.pos_of_ne_zero hN⟩
end GroundTheory.LocalField.Abstract
