-- Prove2me | solution 1 for GlobalTheory.RapidFourier.summable_inv_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:11:35.162391+00:00
-- url     : https://prove2.me/submissions/da0ae7e5-70e5-400a-9b31-f8d3c5372ae1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ContDiffAndFderivTsumFourierOfRapid
import Theorems.Thm_GlobalTheory_RapidFourier_summable_inv_one_add_abs_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real
open GlobalTheory
open GlobalTheory.RapidFourier
namespace GlobalTheory.RapidFourier
theorem _root_.solution (n : ℕ) :
    Summable fun ν : Fin n → ℤ => ((1 + ∑ k, |(ν k : ℝ)|) ^ (2 * n))⁻¹ := by
  have hprod : Summable fun ν : Fin n → ℤ => ∏ k, ((1 + |(ν k : ℝ)|) ^ 2)⁻¹ :=
    GlobalTheory.summable_pi_prod_of_nonneg (f := fun _ (m : ℤ) => ((1 + |(m : ℝ)|) ^ 2)⁻¹)
      (fun _ _ => by positivity) fun _ => summable_inv_one_add_abs_sq
  refine Summable.of_nonneg_of_le (fun ν => by positivity) (fun ν => ?_) hprod
  rw [Finset.prod_inv_distrib]
  apply inv_anti₀ (Finset.prod_pos fun k _ => by positivity)
  calc ∏ k, (1 + |(ν k : ℝ)|) ^ 2 ≤ ∏ _k : Fin n, (1 + ∑ k, |(ν k : ℝ)|) ^ 2 :=
        Finset.prod_le_prod (fun k _ => by positivity) fun k _ =>
          pow_le_pow_left₀ (by positivity)
            (add_le_add le_rfl (Finset.single_le_sum (f := fun k => |(ν k : ℝ)|)
              (fun _ _ => abs_nonneg _) (Finset.mem_univ k))) 2
    _ = (1 + ∑ k, |(ν k : ℝ)|) ^ (2 * n) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm]
end GlobalTheory.RapidFourier
