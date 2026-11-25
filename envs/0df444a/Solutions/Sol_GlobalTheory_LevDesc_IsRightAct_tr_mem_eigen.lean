-- Prove2me | solution 1 for GlobalTheory.LevDesc.IsRightAct.tr_mem_eigen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:59:46.654432+00:00
-- url     : https://prove2.me/submissions/5d5dec19-3006-4a85-a100-6746bf92dd72

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
namespace IsRightAct
theorem _root_.solution {st : G → R →ₐ[K] R} (hs : IsRightAct st) (χ : G →* Kˣ) (F : R) :
    tr st χ F ∈ eigen st χ := fun g => by
  rw [tr_apply, map_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight g) _ _ fun h => ?_
  rw [map_smul, ← hs.2, smul_smul, Equiv.coe_mulRight, map_mul]
  congr 1
  simp
end IsRightAct
end GlobalTheory.LevDesc
