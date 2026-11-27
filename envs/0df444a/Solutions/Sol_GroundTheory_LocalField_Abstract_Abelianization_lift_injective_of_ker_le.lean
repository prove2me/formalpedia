-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.Abelianization.lift_injective_of_ker_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:46:52.203017+00:00
-- url     : https://prove2.me/submissions/35ef8110-5d30-4365-aa81-7463649e7a2f

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_IsoCyclic
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_FunctorialityTransfer
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_IsoPGroup

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
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
namespace GroundTheory.LocalField.Abstract
namespace Abelianization
theorem _root_.solution {Γ T : Type*} [Group Γ] [CommGroup T] (f : Γ →* T)
    (h : f.ker ≤ commutator Γ) : Function.Injective (Abelianization.lift f) := by
  rw [injective_iff_map_eq_one]
  intro z hz
  induction z using QuotientGroup.induction_on with
  | H q =>
    have hq : Abelianization.lift f (Abelianization.of q) = 1 := hz
    rw [Abelianization.lift_apply_of] at hq
    have := h hq
    rw [← Abelianization.ker_of, MonoidHom.mem_ker] at this
    exact this
end Abelianization
end GroundTheory.LocalField.Abstract
