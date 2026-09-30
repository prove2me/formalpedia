-- Prove2me | solution 1 for NonuniformCompetitive.Snoopy.lp_attained
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T10:04:21.485324+00:00
-- url     : https://prove2.me/submissions/58f64418-74af-473d-9d49-7cdbf7abef09

import Definitions.Def_NonuniformCompetitive_Snoopy_ep
import Mathlib.Tactic
open NonuniformCompetitive.Snoopy
open scoped BigOperators

theorem solution (p : ℕ) (hp : 1 ≤ p) (α : ℝ) (π : ℕ → ℝ)
    (hα : α = ep p / (ep p - 1))
    (hπ : ∀ k, π k = (α - 1) * ((((p : ℝ) + 1) / p) ^ (k - 1) - 1)) :
    π (p + 1) = 1 ∧ 0 ≤ π 1 ∧ (∀ k ∈ Finset.Icc 1 p, π k ≤ π (k + 1)) ∧
      ∀ k ≤ p, π (k + 1) * p + ∑ i ∈ Finset.Icc 1 k, (1 - π i) = α * k := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  let r : ℝ := ((p:ℝ)+1)/p
  have hr : 1 < r := by dsimp [r]; apply (lt_div_iff₀ hpR).mpr; linarith
  have hep : ep p=r^p := by unfold ep; congr 1; dsimp [r]; field_simp [ne_of_gt hpR]
  have he : 1 < ep p := by rw [hep]; exact one_lt_pow₀ hr (by omega)
  have hc : 0 < α-1 := by rw [hα]; apply sub_pos.mpr; apply (lt_div_iff₀ (by linarith : 0 < ep p-1)).mpr; linarith
  have heq : (α-1)*(ep p-1)=1 := by rw [hα]; field_simp [ne_of_gt (sub_pos.mpr he)]; ring
  have hpi (k : ℕ) : π (k+1)=(α-1)*(r^k-1) := by rw [hπ]; simp [r]
  refine ⟨?_,?_,?_,?_⟩
  · rw [hpi,← hep,heq]
  · rw [hπ]; simp
  · intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    rw [hπ,hpi]
    apply mul_le_mul_of_nonneg_left _ hc.le
    apply sub_le_sub_right
    change r^(k-1) ≤ r^k
    exact pow_le_pow_right₀ hr.le (by omega)
  · intro k hk
    have hall : ∀ k : ℕ, π (k+1)*(p:ℝ)+∑ i∈Finset.Icc 1 k, (1-π i)=α*k := by
      intro k
      induction k with
      | zero => rw [hpi]; simp
      | succ k ih =>
        have hrec : π (k+2)*(p:ℝ)-(p+1)*π (k+1)=α-1 := by
          rw [hpi (k+1),hpi k,pow_succ]
          dsimp [r]
          field_simp [ne_of_gt hpR]
          ring
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k+1)]
        push_cast
        nlinarith
    exact hall k
