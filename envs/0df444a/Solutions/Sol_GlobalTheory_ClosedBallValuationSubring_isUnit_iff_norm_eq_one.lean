-- Prove2me | solution 1 for GlobalTheory.ClosedBallValuationSubring.isUnit_iff_norm_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:13:29.853798+00:00
-- url     : https://prove2.me/submissions/4e4cdb0a-dbcb-4239-97c2-db3d9c06f527

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ClosedBallValuationSubringToSubring
import Theorems.Thm_GlobalTheory_ClosedBallValuationSubring_mem_closedBallSubring

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ClosedBallValuationSubring
variable (K : Type*) [NormedField K] [IsUltrametricDist K]
variable {K}
namespace GlobalTheory.ClosedBallValuationSubring
theorem _root_.solution {x : closedBallSubring K} : IsUnit x ↔ ‖(x : K)‖ = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have hu : ‖((u : closedBallSubring K) : K)‖ ≤ 1 := (u : closedBallSubring K).2
    have hv : ‖((u⁻¹ : (closedBallSubring K)ˣ) : closedBallSubring K).1‖ ≤ 1 :=
      ((u⁻¹ : (closedBallSubring K)ˣ) : closedBallSubring K).2
    have hprod : ‖((u : closedBallSubring K) : K)‖ *
        ‖((u⁻¹ : (closedBallSubring K)ˣ) : closedBallSubring K).1‖ = 1 := by
      rw [← norm_mul]
      have h := congrArg Subtype.val u.mul_inv
      simp only [Subring.coe_mul, Subring.coe_one] at h
      rw [h, norm_one]
    refine le_antisymm hu ?_
    calc (1 : ℝ) = _ := hprod.symm
      _ ≤ ‖((u : closedBallSubring K) : K)‖ * 1 :=
          mul_le_mul_of_nonneg_left hv (norm_nonneg _)
      _ = _ := mul_one _
  · intro h
    have hx0 : (x : K) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at h
      exact zero_ne_one h
    have hinv : (x : K)⁻¹ ∈ closedBallSubring K := by
      rw [mem_closedBallSubring, norm_inv, h, inv_one]
    refine isUnit_iff_exists_inv.mpr ⟨⟨(x : K)⁻¹, hinv⟩, ?_⟩
    apply Subtype.ext
    simp only [Subring.coe_mul, Subring.coe_one]
    exact mul_inv_cancel₀ hx0
end GlobalTheory.ClosedBallValuationSubring
