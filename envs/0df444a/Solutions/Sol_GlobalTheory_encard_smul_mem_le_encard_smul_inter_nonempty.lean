-- Prove2me | solution 1 for GlobalTheory.encard_smul_mem_le_encard_smul_inter_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:57:19.639195+00:00
-- url     : https://prove2.me/submissions/7af9e86b-ade4-41f9-88a9-74d1ef7e0ca5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EncardSmulMemLeEncardSmulInterNonempty

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal Pointwise
open GlobalTheory
variable {G X : Type*} [Group G] [MulAction G X]
namespace GlobalTheory
theorem _root_.solution (B : Set X) (x : X) :
    {g : G | g • x ∈ B}.encard ≤ {g : G | (g • B ∩ B).Nonempty}.encard := by
  rcases eq_empty_or_nonempty {g : G | g • x ∈ B} with h | ⟨g₀, hg₀⟩
  · simp [h]
  · refine Set.encard_le_encard_of_injOn (f := fun g => g * g₀⁻¹) ?_ ?_
    · intro g hg
      refine ⟨g • x, ⟨g₀ • x, hg₀, ?_⟩, hg⟩
      simp [smul_smul]
    · intro a _ b _ hab
      exact mul_right_cancel hab
end GlobalTheory
