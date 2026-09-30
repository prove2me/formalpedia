-- Prove2me | solution 1 for MarkovChainChoice.Assortment.dual_optimal_tight
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:39:52.291922+00:00
-- url     : https://prove2.me/submissions/6d8216a7-0138-473c-8b6c-ea6b6903c563

import Definitions.Def_MarkovChainChoice_Assortment_LinearPrograms
import Mathlib.Tactic
open Finset MarkovChainChoice.Assortment

theorem solution {n : ℕ} (M : Model n) (r v : Fin n → ℝ)
    (hv : IsDualOptimal M r v) :
    ∀ j, v j = r j ∨ v j = ∑ i, M.rho j i * v i := by
  classical
  intro j
  by_contra h
  push_neg at h
  have hr : r j < v j := lt_of_le_of_ne (hv.1 j).1 h.1.symm
  have hs : (∑ i, M.rho j i * v i) < v j := lt_of_le_of_ne (hv.1 j).2 h.2.symm
  let δ := min (v j-r j) (v j-∑ i, M.rho j i*v i)/2
  have hδ : 0 < δ := div_pos (lt_min (by linarith) (by linarith)) (by norm_num)
  have hδr : δ ≤ v j-r j := by
    have := min_le_left (v j-r j) (v j-∑ i, M.rho j i*v i)
    dsimp [δ] at *
    linarith [lt_min (sub_pos.mpr hr) (sub_pos.mpr hs)]
  have hδs : δ ≤ v j-∑ i, M.rho j i*v i := by
    have := min_le_right (v j-r j) (v j-∑ i, M.rho j i*v i)
    dsimp [δ] at *
    linarith [lt_min (sub_pos.mpr hr) (sub_pos.mpr hs)]
  let w := fun i => if i = j then v i-δ else v i
  have hwle : ∀ i, w i ≤ v i := by intro i; dsimp [w]; split_ifs <;> linarith
  have hw : DualFeasible M r w := by
    intro i
    have hrow : (∑ k, M.rho i k*w k) ≤ ∑ k, M.rho i k*v k :=
      sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left (hwle k) (M.rho_nonneg i k))
    by_cases hi : i = j
    · subst i
      simp only [w,if_pos rfl]
      constructor <;> linarith
    · simp only [w,if_neg hi]
      exact ⟨(hv.1 i).1,hrow.trans (hv.1 i).2⟩
  have he : (∑ i, M.lam i*w i) = (∑ i, M.lam i*v i) - M.lam j*δ := by
    have ht : ∀ i, M.lam i*w i = M.lam i*v i - if i=j then M.lam j*δ else 0 := by
      intro i
      by_cases hi : i=j
      · subst i; simp [w];ring
      · simp [w,hi]
    simp_rw [ht]
    rw [sum_sub_distrib]
    simp
  have hopt := hv.2 w hw
  rw [he] at hopt
  nlinarith [mul_pos (M.lam_pos j) hδ]
