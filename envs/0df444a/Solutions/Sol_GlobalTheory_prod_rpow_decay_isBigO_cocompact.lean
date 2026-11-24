-- Prove2me | solution 1 for GlobalTheory.prod_rpow_decay_isBigO_cocompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:29:56.97333+00:00
-- url     : https://prove2.me/submissions/60677fb1-e6aa-4976-a687-21782e872c05

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdRpowDecayIsBigOCocompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] (g : ι → ℝ → ℂ) (b : ℝ), 0 ≤ b → (∀ i, ∃ C : ℝ, ∀ t : ℝ, ‖g i t‖ ≤ C * (1 + |t|) ^ (-b)) → (fun v : EuclideanSpace ℝ ι => ∏ i, g i (v i)) =O[Filter.cocompact (EuclideanSpace ℝ ι)] (fun v => ‖v‖ ^ (-b)) := by
  intro ι _ g b hb hg
  classical
  choose C hC using hg
  have hC0 : ∀ i, 0 ≤ C i := fun i => by
    have h := hC i 0
    simp only [abs_zero, add_zero, Real.one_rpow, mul_one] at h
    exact (norm_nonneg _).trans h
  set n : ℝ := (Fintype.card ι : ℝ) with hn
  refine Asymptotics.IsBigO.of_bound ((∏ i, C i) * n ^ b) ?_
  have hev : ∀ᶠ v : EuclideanSpace ℝ ι in Filter.cocompact _, 0 < ‖v‖ :=
    tendsto_norm_cocompact_atTop.eventually (Filter.eventually_gt_atTop 0)
  filter_upwards [hev] with v hv
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    have : v = 0 := Subsingleton.elim _ _
    simp [this] at hv
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ (fun i => |v i|) Finset.univ_nonempty
  have hn1 : (1:ℝ) ≤ n := by rw [hn]; exact_mod_cast Fintype.card_pos
  have hnorm : ‖v‖ ≤ n * |v i₀| := by
    have h2 : ‖v‖ ^ 2 ≤ (n * |v i₀|) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      calc ∑ i, ‖v.ofLp i‖ ^ 2 ≤ ∑ _i : ι, |v i₀| ^ 2 := Finset.sum_le_sum fun i _ => by
              rw [Real.norm_eq_abs]
              exact pow_le_pow_left₀ (abs_nonneg _) (hi₀ i (Finset.mem_univ _)) 2
        _ = n * |v i₀| ^ 2 := by simp [hn]
        _ ≤ (n * |v i₀|) ^ 2 := by
              rw [mul_pow]; exact mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2
  have hnpos : 0 < n := by linarith
  have hpos : 0 < ‖v‖ / n := by positivity
  have hle : ‖v‖ / n ≤ 1 + |v i₀| := by
    rw [div_le_iff₀ hnpos]; nlinarith [abs_nonneg (v i₀)]
  have hw : (1 + |v i₀|) ^ (-b) ≤ n ^ b * ‖v‖ ^ (-b) := by
    calc (1 + |v i₀|) ^ (-b) ≤ (‖v‖ / n) ^ (-b) := Real.rpow_le_rpow_of_nonpos hpos hle (by linarith)
      _ = n ^ b * ‖v‖ ^ (-b) := by
        rw [Real.div_rpow (norm_nonneg _) hnpos.le, Real.rpow_neg hnpos.le, div_inv_eq_mul, mul_comm]
  have hrest : ∏ i ∈ Finset.univ.erase i₀, ‖g i (v i)‖ ≤ ∏ i ∈ Finset.univ.erase i₀, C i :=
    Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => (hC i (v i)).trans
      (mul_le_of_le_one_right (hC0 i)
        (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg (v i)]) (by linarith))))
  have h0 : ‖g i₀ (v i₀)‖ ≤ C i₀ * (n ^ b * ‖v‖ ^ (-b)) :=
    (hC i₀ _).trans (mul_le_mul_of_nonneg_left hw (hC0 i₀))
  have hsplitg := Finset.mul_prod_erase Finset.univ (fun i => ‖g i (v i)‖) (Finset.mem_univ i₀)
  have hsplitC := Finset.mul_prod_erase Finset.univ C (Finset.mem_univ i₀)
  rw [norm_prod, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), ← hsplitg, ← hsplitC]
  calc ‖g i₀ (v i₀)‖ * ∏ i ∈ Finset.univ.erase i₀, ‖g i (v i)‖
      ≤ C i₀ * (n ^ b * ‖v‖ ^ (-b)) * ∏ i ∈ Finset.univ.erase i₀, C i :=
        mul_le_mul h0 hrest (Finset.prod_nonneg fun i _ => norm_nonneg _)
          (mul_nonneg (hC0 i₀) (mul_nonneg (Real.rpow_nonneg hnpos.le _) (Real.rpow_nonneg (norm_nonneg _) _)))
    _ = C i₀ * (∏ i ∈ Finset.univ.erase i₀, C i) * n ^ b * ‖v‖ ^ (-b) := by ring
end GlobalTheory
