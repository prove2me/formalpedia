-- Prove2me | solution 1 for MarkovChainChoice.Reduced.H_bounded
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T09:01:54.228988+00:00
-- url     : https://prove2.me/submissions/c8042422-7763-4053-9159-8db1bc2752de

import Definitions.Def_MarkovChainChoice_Reduced_LinearPrograms
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Tactic
open Finset MarkovChainChoice.Reduced

private theorem total_mass {n : ℕ} (M : Model n) (P R : Fin n → ℝ)
    (hb : ∀ j,P j+R j=M.lam j+∑ i,M.rho i j*R i) :
    (∑ j, (P j + (1 - (∑ i, M.rho j i)) * R j)) = ∑ j,M.lam j := by
  have he : (∑ j, (P j + R j)) = ∑ j, (M.lam j + ∑ i, M.rho i j * R i) :=
    sum_congr rfl (fun j hj => hb j)
  simp only [sum_add_distrib] at he
  have hflow : (∑ j,∑ i,M.rho i j*R i) = ∑ i,(∑ j,M.rho i j)*R i := by
    rw [sum_comm]
    simp only [sum_mul]
  rw [hflow] at he
  simp only [sub_mul,one_mul,sum_add_distrib,sum_sub_distrib]
  linarith


theorem solution {n : ℕ} (M : Model n) : Bornology.IsBounded (H M) := by
  classical
  apply isBounded_iff_forall_norm_le.mpr
  cases isEmpty_or_nonempty (Fin n) with
  | inl hn =>
    refine ⟨0,?_⟩
    intro p hp
    simp [Prod.norm_def,Subsingleton.elim p.1 0,Subsingleton.elim p.2 0]
  | inr hn =>
    obtain ⟨k,hk,hmax⟩ := exists_max_image univ (fun j => ∑ i,M.rho j i) univ_nonempty
    let q := ∑ i,M.rho k i
    have hq0 : 0 ≤ q := sum_nonneg (fun i hi => M.rho_nonneg k i)
    have hq1 : q < 1 := M.rho_row_lt_one k
    have hδ : 0 < 1-q := by linarith
    let L := ∑ j,M.lam j
    have hL0 : 0 ≤ L := sum_nonneg (fun j hj => (M.lam_pos j).le)
    refine ⟨L/(1-q),?_⟩
    intro p hp
    have hmass := total_mass M p.1 p.2 hp.2.2
    have hbound (j : Fin n) : p.1 j ≤ L/(1-q) ∧ p.2 j ≤ L/(1-q) := by
      have hterm : p.1 j+(1-∑ i,M.rho j i)*p.2 j ≤ L := by
        dsimp [L]
        rw [← hmass]
        exact single_le_sum (fun i hi => add_nonneg (hp.1 i)
          (mul_nonneg (sub_nonneg.mpr (M.rho_row_lt_one i).le) (hp.2.1 i))) (mem_univ j)
      have hcoef : 0 ≤ (1-∑ i,M.rho j i)*p.2 j :=
        mul_nonneg (sub_nonneg.mpr (M.rho_row_lt_one j).le) (hp.2.1 j)
      have hqj : (∑ i,M.rho j i) ≤ q := hmax j (mem_univ _)
      have hmul : (1-q)*p.2 j ≤ (1-∑ i,M.rho j i)*p.2 j :=
        mul_le_mul_of_nonneg_right (by linarith) (hp.2.1 j)
      constructor
      · apply (le_div_iff₀ hδ).mpr
        nlinarith [hp.1 j]
      · apply (le_div_iff₀ hδ).mpr
        nlinarith [hp.1 j]
    rw [Prod.norm_def]
    apply max_le
    · apply (pi_norm_le_iff_of_nonneg (div_nonneg hL0 hδ.le)).mpr
      intro j
      rw [Real.norm_eq_abs,abs_of_nonneg (hp.1 j)]
      exact (hbound j).1
    · apply (pi_norm_le_iff_of_nonneg (div_nonneg hL0 hδ.le)).mpr
      intro j
      rw [Real.norm_eq_abs,abs_of_nonneg (hp.2.1 j)]
      exact (hbound j).2
