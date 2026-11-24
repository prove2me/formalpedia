-- Prove2me | solution 1 for GlobalTheory.SummCount.summable_rpow_of_fibre_card_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:10:58.461671+00:00
-- url     : https://prove2.me/submissions/22031f55-89a7-4ff8-818a-476f737bbca0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SummableRpowOfFibreCardLe
import Theorems.Thm_GlobalTheory_SummCount_summable_prod_fin_tuple
import Theorems.Thm_GlobalTheory_SummCount_pow_mul_inv_rpow_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SummCount
namespace GlobalTheory.SummCount
theorem _root_.solution (ι : Type) (n : ℕ) (b C t : ℝ) (k : ι → Fin n → ℕ)
    (h : ι → ℝ) (hb : 1 < b) (ht : (n : ℝ) < t)
    (hh : ∀ q, 0 ≤ h q ∧ h q ≤ C * ∏ i, (b ^ k q i)⁻¹)
    (hT : ∀ (m : Fin n → ℕ) (T : Finset ι), (∀ q ∈ T, k q = m) →
      (T.card : ℝ) ≤ C * ∏ i, b ^ (n * m i)) :
    Summable fun q => h q ^ t := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  have ht0 : 0 ≤ t := le_trans (Nat.cast_nonneg n) ht.le
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨q0⟩⟩
  · exact .of_finite
  have hP : ∀ m : Fin n → ℕ, 0 < ∏ i, (b ^ m i)⁻¹ := fun m => by positivity
  have hC : 0 ≤ C := (mul_nonneg_iff_of_pos_right (hP (k q0))).1 ((hh q0).1.trans (hh q0).2)
  set r := b ^ ((n : ℝ) - t) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg hb0.le _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hb (by linarith)
  set g : (Fin n → ℕ) → ℝ := fun m => C * C ^ t * ∏ i, r ^ m i with hg_def
  have hg0 : ∀ m, 0 ≤ g m := fun m => by
    simp only [hg_def]; positivity
  have hg : Summable g :=
    (summable_prod_fin_tuple (summable_geometric_of_lt_one hr0 hr1) (fun _ => pow_nonneg hr0 _)
      n).mul_left _
  have key : ∀ q, h q ^ t ≤ C ^ t * ∏ i, ((b ^ k q i)⁻¹) ^ t := fun q => by
    rw [Real.finset_prod_rpow _ _ (fun i _ => by positivity), ← Real.mul_rpow hC (hP _).le]
    exact Real.rpow_le_rpow (hh q).1 (hh q).2 ht0
  refine summable_of_sum_le (c := ∑' m, g m) (fun q => Real.rpow_nonneg (hh q).1 _) fun T => ?_
  rw [← Finset.sum_fiberwise_of_maps_to (g := k) (t := T.image k)
    (fun q hq => Finset.mem_image_of_mem k hq)]
  refine le_trans (Finset.sum_le_sum fun m _ => ?_) (hg.sum_le_tsum _ (fun m _ => hg0 m))
  calc ∑ q ∈ T with k q = m, h q ^ t
      ≤ ∑ q ∈ T with k q = m, C ^ t * ∏ i, ((b ^ m i)⁻¹) ^ t :=
        Finset.sum_le_sum fun q hq => by
          have := key q
          rwa [(Finset.mem_filter.1 hq).2] at this
    _ = ((T.filter (k · = m)).card : ℝ) * (C ^ t * ∏ i, ((b ^ m i)⁻¹) ^ t) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (C * ∏ i, b ^ (n * m i)) * (C ^ t * ∏ i, ((b ^ m i)⁻¹) ^ t) :=
        mul_le_mul_of_nonneg_right (hT m _ fun q hq => (Finset.mem_filter.1 hq).2)
          (mul_nonneg (Real.rpow_nonneg hC _)
            (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (by positivity) _))
    _ = g m := by
        simp only [hg_def, hr, ← pow_mul_inv_rpow_eq hb0 n, Finset.prod_mul_distrib]
        ring
end GlobalTheory.SummCount
