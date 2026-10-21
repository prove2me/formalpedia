-- Prove2me | solution 1 for LowRankMarkov.RankMLE.lemmaEC1_kl_ge_sq
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T20:29:22.3149+00:00
-- url     : https://prove2.me/submissions/39e7568d-156a-460c-b317-cad73556f774

import Mathlib
import Definitions.Def_LowRankMarkov_RankMLE_Chain
import Definitions.Def_LowRankMarkov_RankMLE_Setting

open LowRankMarkov.RankMLE

namespace LRMKLAux

theorem log_le_quad (K : ℝ) (hK : 1 ≤ K) (s : ℝ) (hs : 0 < s) (hsK : s ≤ K) :
    Real.log s ≤ (s - 1) - (s - 1) ^ 2 / (2 * K ^ 2) := by
  set φ : ℝ → ℝ := fun t => (t - 1) - (t - 1) ^ 2 / (2 * K ^ 2) - Real.log t with hφ
  have hK0 : 0 < K := by linarith
  have hd : ∀ t, 0 < t → HasDerivAt φ (1 - 2 * (t - 1) / (2 * K ^ 2) - t⁻¹) t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ => t - 1) 1 t := (hasDerivAt_id t).sub_const 1
    have h2 : HasDerivAt (fun t : ℝ => (t - 1) ^ 2 / (2 * K ^ 2)) (2 * (t - 1) / (2 * K ^ 2)) t := by
      have := ((h1.mul h1).div_const (2 * K ^ 2))
      refine (this.congr_deriv (by ring)).congr_of_eventuallyEq ?_
      filter_upwards with y
      simp only [Pi.mul_apply]
      ring
    have h3 := Real.hasDerivAt_log ht.ne'
    exact (h1.sub h2).sub h3
  have hcont : ContinuousOn φ (Set.Ioi 0) := by
    intro t ht
    exact (hd t ht).continuousAt.continuousWithinAt
  have hval : ∀ t, 0 < t → t ≤ K → 1 - 2 * (t - 1) / (2 * K ^ 2) - t⁻¹ = (t - 1) * (1 / t - 1 / K ^ 2) := by
    intro t ht _; field_simp; ring
  have hφ1 : φ 1 = 0 := by simp [hφ]
  suffices 0 ≤ φ s by simp only [hφ] at this; linarith
  rw [← hφ1]
  rcases le_or_gt 1 s with h | h
  · -- monotone on [1, K]
    have hmono : MonotoneOn φ (Set.Icc 1 K) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc 1 K)
      · exact hcont.mono (fun t ht => by simp at ht ⊢; linarith [ht.1])
      · intro t ht; simp at ht
        exact (hd t (by linarith [ht.1])).differentiableAt.differentiableWithinAt
      · intro t ht; simp at ht
        rw [(hd t (by linarith [ht.1])).deriv, hval t (by linarith [ht.1]) ht.2.le]
        apply mul_nonneg (by linarith [ht.1])
        rw [sub_nonneg]
        apply one_div_le_one_div_of_le (by linarith [ht.1])
        nlinarith [ht.1, ht.2]
    exact hmono ⟨le_refl 1, hK⟩ ⟨h, hsK⟩ h
  · have hanti : AntitoneOn φ (Set.Icc s 1) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc s 1)
      · exact hcont.mono (fun t ht => by simp at ht ⊢; linarith [ht.1])
      · intro t ht; simp at ht
        exact (hd t (by linarith [ht.1])).differentiableAt.differentiableWithinAt
      · intro t ht; simp at ht
        rw [(hd t (by linarith [ht.1])).deriv, hval t (by linarith [ht.1]) (by linarith [ht.2])]
        apply mul_nonpos_of_nonpos_of_nonneg (by linarith [ht.2])
        rw [sub_nonneg]
        apply one_div_le_one_div_of_le (by linarith [ht.1])
        nlinarith [ht.1, ht.2]
    exact hanti ⟨le_refl s, h.le⟩ ⟨h.le, le_refl 1⟩ h.le

theorem term_bound {p : ℕ} (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hp : 0 < (p : ℝ))
    (u v : ℝ)
    (hu : u = 0 ∨ (α / (p : ℝ) ≤ u ∧ u ≤ β / (p : ℝ)))
    (hv : α / (p : ℝ) ≤ v ∧ v ≤ β / (p : ℝ)) :
    (p : ℝ) * α / (2 * β ^ 2) * (u - v) ^ 2 ≤
      (if u = 0 then 0 else u * Real.log (u / v)) - (u - v) := by
  have hab : α ≤ β := by
    have := hv.1.trans hv.2
    rwa [div_le_div_iff_of_pos_right hp] at this
  have hv0 : 0 < v := lt_of_lt_of_le (div_pos hα hp) hv.1
  rcases hu with hu0 | ⟨hu1, hu2⟩
  · subst hu0
    simp only [if_true]
    -- c v^2 ≤ v
    have : (p : ℝ) * α / (2 * β ^ 2) * v ≤ 1 := by
      have h1 : (p : ℝ) * α / (2 * β ^ 2) * v ≤ (p : ℝ) * α / (2 * β ^ 2) * (β / p) :=
        mul_le_mul_of_nonneg_left hv.2 (by positivity)
      have h2 : (p : ℝ) * α / (2 * β ^ 2) * (β / p) = α / (2 * β) := by
        field_simp
      have h3 : α / (2 * β) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      linarith
    nlinarith
  · have hu0 : 0 < u := lt_of_lt_of_le (div_pos hα hp) hu1
    rw [if_neg hu0.ne']
    set b := β / (p : ℝ)
    have hb : 0 < b := div_pos hβ hp
    have hK : 1 ≤ b / u := by rw [le_div_iff₀ hu0]; linarith
    have hs : 0 < v / u := div_pos hv0 hu0
    have hsK : v / u ≤ b / u := div_le_div_of_nonneg_right hv.2 hu0.le
    have key := log_le_quad (b / u) hK (v / u) hs hsK
    have hlog : Real.log (u / v) = - Real.log (v / u) := by
      rw [← Real.log_inv, inv_div]
    rw [hlog]
    -- u * (-log s) ≥ u*(1-s) + u*(s-1)^2/(2K^2)
    have e1 : u * ((v / u - 1) - (v / u - 1) ^ 2 / (2 * (b / u) ^ 2))
        = (v - u) - u * (v - u) ^ 2 / (2 * b ^ 2) := by
      field_simp
    have h1 : u * Real.log (v / u) ≤ (v - u) - u * (v - u) ^ 2 / (2 * b ^ 2) := by
      rw [← e1]; exact mul_le_mul_of_nonneg_left key hu0.le
    have h2 : (p : ℝ) * α / (2 * β ^ 2) * (u - v) ^ 2 ≤ u * (v - u) ^ 2 / (2 * b ^ 2) := by
      have e2 : (p : ℝ) * α / (2 * β ^ 2) = (α / p) / (2 * b ^ 2) := by
        simp only [b]; field_simp
      rw [e2, div_mul_eq_mul_div, show (u - v) ^ 2 = (v - u) ^ 2 by ring]
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right hu1 (sq_nonneg _)
    linarith

end LRMKLAux

open LRMKLAux in
theorem solution {p : ℕ} (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (u v : Fin p → ℝ) (hu_sum : ∑ j, u j = 1) (hv_sum : ∑ j, v j = 1)
    (hu : ∀ j, u j = 0 ∨ (α / (p : ℝ) ≤ u j ∧ u j ≤ β / (p : ℝ)))
    (hv : ∀ j, α / (p : ℝ) ≤ v j ∧ v j ≤ β / (p : ℝ)) :
    (p : ℝ) * α / (2 * β ^ 2) * ∑ j, (u j - v j) ^ 2 ≤ klVec u v := by
  rcases Nat.eq_zero_or_pos p with hp0 | hp0
  · subst hp0; simp at hu_sum
  have hp : 0 < (p : ℝ) := by exact_mod_cast hp0
  have hsum0 : ∑ j, (u j - v j) = 0 := by
    rw [Finset.sum_sub_distrib, hu_sum, hv_sum]; ring
  unfold klVec
  rw [Finset.mul_sum]
  calc ∑ j, (p : ℝ) * α / (2 * β ^ 2) * (u j - v j) ^ 2
      ≤ ∑ j, ((if u j = 0 then 0 else u j * Real.log (u j / v j)) - (u j - v j)) :=
        Finset.sum_le_sum fun j _ => term_bound α β hα hβ hp (u j) (v j) (hu j) (hv j)
    _ = ∑ j, (if u j = 0 then 0 else u j * Real.log (u j / v j)) := by
        rw [Finset.sum_sub_distrib, hsum0, sub_zero]
