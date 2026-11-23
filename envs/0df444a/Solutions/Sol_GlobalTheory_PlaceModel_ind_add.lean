-- Prove2me | solution 1 for GlobalTheory.PlaceModel.ind_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:30:35.086988+00:00
-- url     : https://prove2.me/submissions/95235b41-5ba7-485d-9c5c-50f24f37e853

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LinearIndependentWave

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PlaceModel
variable {G : Type} [AddCommGroup G]
variable {χ : G → G → ℂ} {X Y L L' : AddSubgroup G}
namespace GlobalTheory.PlaceModel
theorem _root_.solution (L : AddSubgroup G) (t : G) {u : G} (hu : u ∈ L) : ind L (t + u) = ind L t := by
  unfold ind
  by_cases ht : t ∈ L
  · rw [if_pos ht, if_pos ((L.add_mem_cancel_right hu).mpr ht)]
  · rw [if_neg ht, if_neg fun h' => ht ((L.add_mem_cancel_right hu).mp h')]
end GlobalTheory.PlaceModel
