-- Prove2me | solution 1 for GlobalTheory.RelIndexOfMap.relIndex_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:16:28.031135+00:00
-- url     : https://prove2.me/submissions/8a1d5fb7-91d3-4d81-9fa0-3907fb843d34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RelIndexEqOfMap
import Theorems.Thm_GlobalTheory_RelIndexOfMap_relIndex_eq_of_map
import Theorems.Thm_GlobalTheory_RelIndexOfMap_index_pi_dep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.RelIndexOfMap
namespace GlobalTheory.RelIndexOfMap
theorem _root_.solution {ι : Type} [Fintype ι] {H : ι → Type} [∀ i, Group (H i)]
    (U V : ∀ i, Subgroup (H i)) :
    (Subgroup.pi Set.univ V).relIndex (Subgroup.pi Set.univ U) = ∏ i, (V i).relIndex (U i) := by
  let f : (∀ i, U i) →* (∀ i, H i) :=
    { toFun := fun x i => (x i : H i)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have h := relIndex_eq_of_map f ⊤ (Subgroup.pi Set.univ fun i => (V i).subgroupOf (U i))
    (Subgroup.pi Set.univ U) (Subgroup.pi Set.univ V) (by
      ext u
      constructor
      · rintro ⟨x, -, rfl⟩ i _
        exact (x i).2
      · intro hu
        exact ⟨fun i => ⟨u i, hu i trivial⟩, trivial, rfl⟩) (by
      intro a _
      exact Iff.rfl)
  rw [← h, Subgroup.relIndex_top_right]
  exact index_pi_dep (fun i => (V i).subgroupOf (U i))
end GlobalTheory.RelIndexOfMap
