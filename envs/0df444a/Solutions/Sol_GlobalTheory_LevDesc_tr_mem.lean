-- Prove2me | solution 1 for GlobalTheory.LevDesc.tr_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:04:18.818561+00:00
-- url     : https://prove2.me/submissions/7e235ecb-35d7-4960-a010-5f993cd22616

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsRightActFunPull
import Theorems.Thm_GlobalTheory_LevDesc_tr_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LevDesc
variable {G K R : Type} [Group G] [Field K] [CommRing R] [Algebra K R]
variable (st : G → R →ₐ[K] R)
variable [Fintype G]
namespace GlobalTheory.LevDesc
theorem _root_.solution {C : Submodule K R} (hC : ∀ h, ∀ x ∈ C, st h x ∈ C) (χ : G →* Kˣ) {x : R} (hx : x ∈ C) :
    tr st χ x ∈ C := by
  rw [tr_apply]; exact C.sum_mem fun g _ => C.smul_mem _ (hC _ x hx)
end GlobalTheory.LevDesc
