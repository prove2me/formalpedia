-- Prove2me | solution 1 for GlobalTheory.GramCount.Prim.eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:56:19.303019+00:00
-- url     : https://prove2.me/submissions/93449d42-de90-4c61-97e8-e0ac05bd679d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Theorems.Thm_GlobalTheory_GramCount_ip_zero_left
import Theorems.Thm_GlobalTheory_GramCount_ip_smul_left
import Theorems.Thm_GlobalTheory_GramCount_ip_sum_left

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
namespace Prim
theorem _root_.solution {m : ℕ} {x : Fin m → Fin n → A} (h : Prim c x) (s : Fin m → A)
    (hs : ∑ a, s a • x a = 0) : s = 0 := by

  unfold Prim at h
  obtain ⟨y, hy⟩ := h
  funext b
  have hb := congrArg (fun z => ip c z (y b)) hs
  simp only [ip_sum_left, ip_smul_left, hy, ip_zero_left] at hb
  simpa using hb
end Prim
end GlobalTheory.GramCount
