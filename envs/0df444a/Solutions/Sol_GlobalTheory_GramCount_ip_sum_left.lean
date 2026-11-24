-- Prove2me | solution 1 for GlobalTheory.GramCount.ip_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:36:37.578205+00:00
-- url     : https://prove2.me/submissions/d4882442-abb8-40cc-8334-e9f59a5bc386

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
theorem _root_.solution {ι : Type} (s : Finset ι) (x : ι → Fin n → A) (y : Fin n → A) :
    ip c (∑ a ∈ s, x a) y = ∑ a ∈ s, ip c (x a) y := by
  unfold ip
  simp only [Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm
end GlobalTheory.GramCount
