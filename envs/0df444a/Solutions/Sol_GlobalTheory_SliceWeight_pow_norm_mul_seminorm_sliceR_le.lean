-- Prove2me | solution 1 for GlobalTheory.SliceWeight.pow_norm_mul_seminorm_sliceR_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:15:07.381655+00:00
-- url     : https://prove2.me/submissions/59994d8f-c62d-4fe8-bb7e-374b82fac884

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthElim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClmSupBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowNormMulSeminormSliceRLe
import Theorems.Thm_GlobalTheory_SliceWeight_norm_le_norm_elim_left
import Theorems.Thm_GlobalTheory_SliceWeight_iteratedFDeriv_sliceR_norm_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
open scoped ContDiff
noncomputable section
open GlobalTheory GlobalTheory.SliceWeight
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace GlobalTheory.SliceWeight
theorem _root_.solution (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (κ κ' : Type) [Fintype κ] [Fintype κ'] (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (a k n : ℕ) (x : κ → V) :
    ‖x‖ ^ a * SchwartzMap.seminorm ℂ k n (sliceR f x) ≤ SchwartzMap.seminorm ℂ (a + k) n f := by
  have hpt : ∀ y : κ' → V, ‖x‖ ^ a * (‖y‖ ^ k * ‖iteratedFDeriv ℝ n (sliceR f x) y‖)
      ≤ SchwartzMap.seminorm ℂ (a + k) n f := by
    intro y
    have h1 := iteratedFDeriv_sliceR_norm_le f x n y
    have hx := norm_le_norm_elim_left x y
    have hy := norm_le_norm_elim x y
    calc ‖x‖ ^ a * (‖y‖ ^ k * ‖iteratedFDeriv ℝ n (sliceR f x) y‖)
        ≤ ‖(Sum.elim x y : κ ⊕ κ' → V)‖ ^ a * (‖(Sum.elim x y : κ ⊕ κ' → V)‖ ^ k
            * ‖iteratedFDeriv ℝ n f (Sum.elim x y)‖) := by gcongr
      _ = ‖(Sum.elim x y : κ ⊕ κ' → V)‖ ^ (a + k) * ‖iteratedFDeriv ℝ n f (Sum.elim x y)‖ := by
          rw [pow_add, mul_assoc]
      _ ≤ _ := SchwartzMap.le_seminorm ℂ (a + k) n f _
  rcases eq_or_lt_of_le (pow_nonneg (norm_nonneg x) a) with h0 | hpos
  · rw [← h0, zero_mul]; exact apply_nonneg _ _
  · rw [mul_comm, ← le_div_iff₀ hpos]
    refine SchwartzMap.seminorm_le_bound ℂ k n _ (div_nonneg (apply_nonneg _ _) hpos.le) fun y => ?_
    rw [le_div_iff₀ hpos, mul_comm]
    exact hpt y
end GlobalTheory.SliceWeight
