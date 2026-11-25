-- Prove2me | solution 1 for GlobalTheory.LevDesc.tr_of_mem_eigen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:04:20.188872+00:00
-- url     : https://prove2.me/submissions/5bd85670-941d-4851-8a43-b7b1c279ba8d

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
theorem _root_.solution {χ : G →* Kˣ} {F : R} (hF : F ∈ eigen st χ) : tr st χ F = (Fintype.card G : K) • F := by
  rw [tr_apply, Finset.sum_congr rfl (g := fun _ => F) fun h _ => by rw [hF h, smul_smul]; simp]
  simp [Nat.cast_smul_eq_nsmul]
end GlobalTheory.LevDesc
