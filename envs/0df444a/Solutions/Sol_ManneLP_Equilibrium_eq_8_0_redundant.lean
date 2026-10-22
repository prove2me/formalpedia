-- Prove2me | solution 1 for ManneLP.Equilibrium.eq_8_0_redundant
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:08:31.272436+00:00
-- url     : https://prove2.me/submissions/ad5c48d5-5e38-420c-b6bf-6dfe578e56a8

import Mathlib
import Definitions.Def_ManneLP_Equilibrium_Model
import Definitions.Def_ManneLP_Equilibrium_LP
set_option autoImplicit false
open ManneLP.Equilibrium

theorem EF_pw (c : ℝ) (u v T n : ℕ) (hk : u + v ≤ T) :
    (if (u:ℤ) + (v:ℤ) - (n:ℤ) ≤ 0 then c else 0) +
      ∑ i ∈ Finset.range T, (if (u:ℤ) + (v:ℤ) - (n:ℤ) = ((i + 1 : ℕ) : ℤ) then c else 0) = c := by
  by_cases h : (u:ℤ) + (v:ℤ) - (n:ℤ) ≤ 0
  · rw [if_pos h, Finset.sum_eq_zero, add_zero]
    intro i _
    rw [if_neg]
    omega
  · rw [if_neg h, zero_add, Finset.sum_eq_single (u + v - n - 1)]
    · rw [if_pos]
      omega
    · intro i _ hne
      rw [if_neg]
      omega
    · intro hnm
      exfalso
      apply hnm
      rw [Finset.mem_range]
      omega

theorem solution (M : Model) (x : ℕ × ℕ → ℝ)
    (h4 : ∑ a ∈ M.A, x a = 1) (h8 : ∀ t : ℕ, 1 ≤ t → t ≤ M.T → Eq8t M x t) :
    Eq80 M x := by
  have hsum := M.p_hasSum.summable
  have summ : ∀ (a : ℕ × ℕ) (P : ℕ → Prop) (_ : DecidablePred P),
      Summable (fun n : ℕ => if P n then M.p n * x a else 0) := by
    intro a P _
    refine Summable.of_norm_bounded (hsum.mul_right |x a|) (fun n => ?_)
    split_ifs
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (M.p_nonneg n)]
    · simp only [norm_zero]
      have := M.p_nonneg n
      positivity
  have F1 : ∑ t ∈ Finset.range (M.T + 1), marginal M x t = ∑ a ∈ M.A, x a := by
    unfold marginal actions
    simp_rw [Finset.sum_filter]
    rw [← Finset.sum_product (f := fun p : ℕ × ℕ => if p ∈ M.A then x p else 0)
      (s := Finset.range (M.T + 1)) (t := Finset.range (M.T + 1))]
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.2]
    intro a ha
    have := M.A_le a ha
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    omega
  have F2 : rhsZero M x + ∑ i ∈ Finset.range M.T, rhsPos M x (i + 1) = ∑ a ∈ M.A, x a := by
    unfold rhsZero rhsPos
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    rw [← Summable.tsum_finsetSum (fun i _ => summ a _ _),
      ← Summable.tsum_add (summ a _ _) (summable_sum (fun i _ => summ a _ _))]
    have : ∀ n : ℕ, ((if (a.1 : ℤ) + (a.2 : ℤ) - (n : ℤ) ≤ 0 then M.p n * x a else 0) +
        ∑ i ∈ Finset.range M.T,
          (if (a.1 : ℤ) + (a.2 : ℤ) - (n : ℤ) = ((i + 1 : ℕ) : ℤ) then M.p n * x a else 0)) =
        M.p n * x a := fun n => EF_pw _ a.1 a.2 M.T n (M.A_le a ha)
    rw [tsum_congr this, tsum_mul_right, M.p_hasSum.tsum_eq, one_mul]
  unfold Eq80
  rw [Finset.sum_range_succ'] at F1
  have h5 : ∑ i ∈ Finset.range M.T, marginal M x (i + 1) =
      ∑ i ∈ Finset.range M.T, rhsPos M x (i + 1) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    exact h8 (i + 1) (by omega) (by omega)
  linarith
