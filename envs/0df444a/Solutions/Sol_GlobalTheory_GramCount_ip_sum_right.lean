-- Prove2me | solution 1 for GlobalTheory.GramCount.ip_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:53:49.282575+00:00
-- url     : https://prove2.me/submissions/9deee15e-add6-4a39-b754-04b4156727cb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.GramCount
variable {A : Type} [CommRing A]
variable (c : A →+* A) {n : ℕ}
namespace GlobalTheory.GramCount
theorem _root_.solution {ι : Type} (s : Finset ι) (x : Fin n → A) (y : ι → Fin n → A) :
    ip c x (∑ a ∈ s, y a) = ∑ a ∈ s, ip c x (y a) := by
  unfold ip
  simp only [Finset.sum_apply, map_sum, Finset.mul_sum]
  exact Finset.sum_comm
end GlobalTheory.GramCount
