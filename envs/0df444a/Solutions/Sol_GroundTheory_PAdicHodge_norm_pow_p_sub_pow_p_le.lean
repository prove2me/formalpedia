-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_pow_p_sub_pow_p_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:18:59.330092+00:00
-- url     : https://prove2.me/submissions/81be9c0b-20a7-4ecd-978d-c196b5909409

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_UnramifiedClosureCountableNeighbourhoods
import Definitions.Def_GroundTheory_PAdicHodge_UnramifiedClosure
import Theorems.Thm_GroundTheory_PAdicHodge_norm_pow_sub_pow_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open Polynomial Filter Topology
variable (p : ℕ) [hp : Fact p.Prime]
variable {p}
variable {F : Type*} [NormedField F] [IsUltrametricDist F]
omit hp
namespace GroundTheory.PAdicHodge
theorem _root_.solution {a b : F} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hp1 : ‖(p : F)‖ ≤ 1)
    {e : ℕ} (he : 1 ≤ e) (hab : ‖a - b‖ ≤ ‖(p : F)‖ ^ e) :
    ‖a ^ p - b ^ p‖ ≤ ‖(p : F)‖ ^ (e + 1) := by
  rw [← geom_sum₂_mul, norm_mul, pow_succ, mul_comm (‖(p : F)‖ ^ e)]
  refine mul_le_mul ?_ hab (norm_nonneg _) (norm_nonneg _)
  have hsum : ∑ i ∈ Finset.range p, b ^ i * b ^ (p - 1 - i) = (p : F) * b ^ (p - 1) := by
    rw [Finset.sum_congr rfl fun i hi => (by
      rw [← pow_add]; congr 1; have := Finset.mem_range.1 hi; omega :
        b ^ i * b ^ (p - 1 - i) = b ^ (p - 1)), Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hsplit : ∑ i ∈ Finset.range p, a ^ i * b ^ (p - 1 - i) =
      (p : F) * b ^ (p - 1) + ∑ i ∈ Finset.range p, (a ^ i - b ^ i) * b ^ (p - 1 - i) := by
    rw [← hsum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsplit]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hb)
  · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
    rw [norm_mul, norm_pow]
    have hpe : ‖(p : F)‖ ^ e ≤ ‖(p : F)‖ := by
      calc ‖(p : F)‖ ^ e ≤ ‖(p : F)‖ ^ 1 := pow_le_pow_of_le_one (norm_nonneg _) hp1 he
        _ = ‖(p : F)‖ := pow_one _
    exact (mul_le_mul (((norm_pow_sub_pow_le ha hb i).trans hab).trans hpe)
      (pow_le_one₀ (norm_nonneg _) hb) (by positivity) (norm_nonneg _)).trans (mul_one _).le
end GroundTheory.PAdicHodge
