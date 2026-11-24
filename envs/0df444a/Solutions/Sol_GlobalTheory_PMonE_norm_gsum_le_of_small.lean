-- Prove2me | solution 1 for GlobalTheory.PMonE.norm_gsum_le_of_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:18:43.769076+00:00
-- url     : https://prove2.me/submissions/d1de1f0d-6d6d-4c7f-b3fb-7504b18b4611

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUniqueIntegralAdditiveSystemFrobeniusPower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PMonE Finset
open GlobalTheory GlobalTheory.PMonE
namespace GlobalTheory.PMonE
theorem _root_.solution {F : Type*} [NormedField F] [IsUltrametricDist F] {m : Type*} [Fintype m]
    (q D : ℕ) (hq : 0 < q) (M : ℕ → Matrix m m F) (δ : ℝ) (hδ : 0 ≤ δ)
    (hM : ∀ n, n ≤ D → ∀ i j, ‖M n i j‖ ≤ δ) (z : m → F) (hz : ‖z‖ ≤ 1) :
    ‖gsum q D M z‖ ≤ δ * ‖z‖ := by
  have h0 : 0 ≤ δ * ‖z‖ := mul_nonneg hδ (norm_nonneg _)
  rw [pi_norm_le_iff_of_nonneg h0]
  intro i
  unfold gsum
  rw [Finset.sum_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg h0 fun n hn => ?_
  simp only [Matrix.mulVec, dotProduct]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg h0 fun j _ => ?_
  rw [norm_mul, norm_pow]
  have hj : ‖z j‖ ≤ ‖z‖ := norm_le_pi_norm z j
  refine mul_le_mul (hM n (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)) i j) ?_ (by positivity) hδ
  exact (pow_le_of_le_one (norm_nonneg _) (hj.trans hz) (pow_pos hq n).ne').trans hj
end GlobalTheory.PMonE
