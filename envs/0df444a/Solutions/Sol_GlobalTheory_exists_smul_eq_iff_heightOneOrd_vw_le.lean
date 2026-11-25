-- Prove2me | solution 1 for GlobalTheory.exists_smul_eq_iff_heightOneOrd_vw_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:06:36.876448+00:00
-- url     : https://prove2.me/submissions/922b8a7a-a2e1-4674-adfd-5270b8f703e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Theorems.Thm_GlobalTheory_heightOneOrd_vw_div
import Theorems.Thm_GlobalTheory_mem_range_algebraMap_iff_heightOneOrd_vw_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors TensorProduct WithZero
open GlobalTheory
variable {A : Type*} [CommRing A] [IsDomain A]
variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
variable {K}
variable [IsNoetherianRing A]
variable [IsIntegrallyClosed A]
namespace GlobalTheory
theorem _root_.solution {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    (∃ a : A, a • y = x) ↔ ∀ (p : Ideal A) [p.IsPrime] (hp : p.height = 1),
      heightOneOrd_vw p hp y ≤ heightOneOrd_vw p hp x := by
  have h := mem_range_algebraMap_iff_heightOneOrd_vw_nonneg (A := A) (div_ne_zero hx hy)
  simp only [heightOneOrd_vw_div _ _ hx hy, sub_nonneg] at h
  rw [← h, RingHom.mem_range]
  exact exists_congr fun a => by rw [Algebra.smul_def, eq_div_iff hy]
end GlobalTheory
