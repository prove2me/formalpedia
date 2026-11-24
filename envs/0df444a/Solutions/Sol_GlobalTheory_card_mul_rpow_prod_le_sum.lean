-- Prove2me | solution 1 for GlobalTheory.card_mul_rpow_prod_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:25:52.989839+00:00
-- url     : https://prove2.me/submissions/04af9046-5221-4741-b5c3-27f04b229e41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped nonZeroDivisors
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {ι : Type*} [Fintype ι] [Nonempty ι] (z : ι → ℝ)
    (hz : ∀ i, 0 ≤ z i) :
    (Fintype.card ι : ℝ) * (∏ i, z i) ^ ((Fintype.card ι : ℝ)⁻¹) ≤ ∑ i, z i := by
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have h := Real.geom_mean_le_arith_mean_weighted Finset.univ
    (fun _ : ι => (Fintype.card ι : ℝ)⁻¹) z (fun _ _ => by positivity)
    (by simp [hc.ne']) (fun i _ => hz i)
  rw [Real.finsetProd_rpow _ _ (fun i _ => hz i), ← Finset.mul_sum] at h
  calc _ ≤ (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ)⁻¹ * ∑ i, z i) := by gcongr
    _ = _ := by field_simp
end GlobalTheory
