-- Prove2me | solution 1 for JacksonJobshop.Equilibrium.product_form_satisfies_balance
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T03:23:09.58333+00:00
-- url     : https://prove2.me/submissions/f943b6d0-966d-48a2-84a9-a12c85592e69

import Mathlib
import Definitions.Def_JacksonJobshop_Equilibrium_System

set_option autoImplicit false

namespace JacksonJobshop.Equilibrium

private lemma S_update_succ {N : ℕ} (k : Fin N → ℕ) (n : Fin N) :
    S (Function.update k n (k n + 1)) = S k + 1 := by
  unfold S
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ n),
      ← Finset.add_sum_erase _ (fun j => k j) (Finset.mem_univ n)]
  rw [Function.update_self]
  have h : ∑ x ∈ Finset.univ.erase n, Function.update k n (k n + 1) x =
      ∑ x ∈ Finset.univ.erase n, k x :=
    Finset.sum_congr rfl fun x hx => Function.update_of_ne (Finset.ne_of_mem_erase hx) _ _
  rw [h]
  omega

private lemma S_pos_of_pos {N : ℕ} (k : Fin N → ℕ) (m : Fin N) (hm : 0 < k m) :
    0 < S k := by
  unfold S
  have hle : k m ≤ ∑ n, k n :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ m)
  omega

private lemma S_update_pred {N : ℕ} (k : Fin N → ℕ) (m : Fin N) (hm : 0 < k m) :
    S (Function.update k m (k m - 1)) = S k - 1 := by
  have hk : Function.update (Function.update k m (k m - 1)) m
      (Function.update k m (k m - 1) m + 1) = k := by
    ext j
    by_cases hj : j = m
    · subst hj
      simp only [Function.update_self]
      omega
    · simp [Function.update_of_ne hj]
  have h := S_update_succ (Function.update k m (k m - 1)) m
  rw [hk] at h
  omega

private lemma W_succ {N : ℕ} (sys : JobshopSystem N) (K : ℕ) :
    W sys (K + 1) = sys.lam K * W sys K := by
  unfold W
  rw [Finset.prod_range_succ, mul_comm]

private lemma lam_mul_W_pred {N : ℕ} (sys : JobshopSystem N) {K : ℕ} (hK : 0 < K) :
    sys.lam (K - 1) * W sys (K - 1) = W sys K := by
  have h := W_succ sys (K - 1)
  rw [Nat.sub_add_cancel hK] at h
  exact h.symm

private lemma w_update_succ {N : ℕ} (sys : JobshopSystem N) (k : Fin N → ℕ) (n : Fin N) :
    sys.mu n (k n + 1) * w sys (Function.update k n (k n + 1)) = sys.e n * w sys k := by
  unfold w
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ n),
      ← Finset.mul_prod_erase _ (fun j => ∏ i ∈ Finset.Icc 1 (k j), sys.e j / sys.mu j i)
        (Finset.mem_univ n)]
  rw [Function.update_self]
  have hrest :
      ∏ x ∈ Finset.univ.erase n,
        ∏ i ∈ Finset.Icc 1 (Function.update k n (k n + 1) x), sys.e x / sys.mu x i =
      ∏ x ∈ Finset.univ.erase n,
        ∏ i ∈ Finset.Icc 1 (k x), sys.e x / sys.mu x i :=
    Finset.prod_congr rfl fun x hx => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
  rw [hrest, Finset.prod_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le _))]
  have hmu : sys.mu n (k n + 1) ≠ 0 := ne_of_gt (sys.mu_pos n (k n + 1) (Nat.succ_pos _))
  field_simp [hmu]

private lemma w_update_pred {N : ℕ} (sys : JobshopSystem N) (k : Fin N → ℕ) (m : Fin N)
    (hm : 0 < k m) :
    sys.mu m (k m) * w sys k = sys.e m * w sys (Function.update k m (k m - 1)) := by
  have hk : Function.update (Function.update k m (k m - 1)) m
      (Function.update k m (k m - 1) m + 1) = k := by
    ext j
    by_cases hj : j = m
    · subst hj
      simp only [Function.update_self]
      omega
    · simp [Function.update_of_ne hj]
  have h := w_update_succ sys (Function.update k m (k m - 1)) m
  rw [hk] at h
  have hkm : Function.update k m (k m - 1) m + 1 = k m := by
    simp only [Function.update_self]
    omega
  rwa [hkm] at h

private lemma sum_e_mul_r_exit {N : ℕ} (sys : JobshopSystem N) :
    ∑ m, sys.e m * sys.r (some m) none = ∑ n, sys.r none (some n) := by
  have hsum : ∑ n, sys.e n =
      (∑ n, sys.r none (some n)) + ∑ n, ∑ m, sys.e m * sys.r (some m) (some n) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => sys.e_traffic n
  rw [Finset.sum_comm] at hsum
  have hinner : ∑ m, ∑ n, sys.e m * sys.r (some m) (some n) =
      (∑ m, sys.e m) - ∑ m, sys.e m * sys.r (some m) none := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Finset.mul_sum]
    have hr := sys.r_sum (some m)
    rw [Fintype.sum_option] at hr
    have hr' : ∑ n, sys.r (some m) (some n) = 1 - sys.r (some m) none := by linarith
    rw [hr']
    ring
  rw [hinner] at hsum
  linarith

private lemma balance_unscaled {N : ℕ} (sys : JobshopSystem N) (k : Fin N → ℕ) :
    Balance sys (fun k => w sys k * W sys (S k)) k := by
  unfold Balance
  -- Simplify Term 3 (departures from the system)
  have hterm3 :
      ∑ n, sys.mu n (k n + 1) * sys.r (some n) none *
        (w sys (Function.update k n (k n + 1)) * W sys (S (Function.update k n (k n + 1)))) =
      sys.lam (S k) * (∑ n, sys.r none (some n)) * (w sys k * W sys (S k)) := by
    have h1 : ∀ n,
        sys.mu n (k n + 1) * sys.r (some n) none *
          (w sys (Function.update k n (k n + 1)) * W sys (S (Function.update k n (k n + 1)))) =
        (sys.e n * sys.r (some n) none) * (sys.lam (S k) * (w sys k * W sys (S k))) := by
      intro n
      rw [S_update_succ, W_succ]
      have hw := w_update_succ sys k n
      calc
        sys.mu n (k n + 1) * sys.r (some n) none *
            (w sys (Function.update k n (k n + 1)) * (sys.lam (S k) * W sys (S k)))
            = (sys.mu n (k n + 1) * w sys (Function.update k n (k n + 1))) *
                sys.r (some n) none * (sys.lam (S k) * W sys (S k)) := by ring
        _ = (sys.e n * w sys k) * sys.r (some n) none * (sys.lam (S k) * W sys (S k)) := by
              rw [hw]
        _ = (sys.e n * sys.r (some n) none) * (sys.lam (S k) * (w sys k * W sys (S k))) := by
              ring
    simp_rw [h1]
    rw [← Finset.sum_mul, sum_e_mul_r_exit]
    ring
  -- Simplify Term 2 (external arrivals)
  have hterm2 :
      ∑ m, (if 0 < k m then
        sys.lam (S k - 1) * sys.r none (some m) *
          (w sys (Function.update k m (k m - 1)) * W sys (S (Function.update k m (k m - 1))))
        else 0) =
      (∑ m, if 0 < k m then sys.r none (some m) * w sys (Function.update k m (k m - 1)) else 0) *
        W sys (S k) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs with hm
    · rw [S_update_pred k m hm]
      have hW := lam_mul_W_pred sys (S_pos_of_pos k m hm)
      calc
        sys.lam (S k - 1) * sys.r none (some m) *
            (w sys (Function.update k m (k m - 1)) * W sys (S k - 1))
            = sys.r none (some m) * w sys (Function.update k m (k m - 1)) *
                (sys.lam (S k - 1) * W sys (S k - 1)) := by ring
        _ = sys.r none (some m) * w sys (Function.update k m (k m - 1)) * W sys (S k) := by
              rw [hW]
    · ring
  -- Simplify Term 4 (internal transfers)
  have hterm4 :
      ∑ m, ∑ n, (if m ≠ n ∧ 0 < k m then
        sys.mu n (k n + 1) * sys.r (some n) (some m) *
          (w sys (Function.update (Function.update k m (k m - 1)) n (k n + 1)) *
            W sys (S (Function.update (Function.update k m (k m - 1)) n (k n + 1))))
        else 0) =
      (∑ m, if 0 < k m then
        (∑ n, if m ≠ n then sys.e n * sys.r (some n) (some m) else 0) *
          w sys (Function.update k m (k m - 1))
        else 0) * W sys (S k) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases hm : 0 < k m
    · rw [if_pos hm, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun n _ => ?_
      by_cases hmn : m ≠ n
      · rw [if_pos ⟨hmn, hm⟩, if_pos hmn]
        set k' := Function.update k m (k m - 1)
        have hkn : k' n = k n := Function.update_of_ne (Ne.symm hmn) _ _
        have hS : S (Function.update k' n (k n + 1)) = S k := by
          rw [← hkn, S_update_succ, S_update_pred k m hm,
              Nat.sub_add_cancel (S_pos_of_pos k m hm)]
        have hw : sys.mu n (k n + 1) * w sys (Function.update k' n (k n + 1)) =
            sys.e n * w sys k' := by
          rw [← hkn]
          exact w_update_succ sys k' n
        rw [hS]
        calc
          sys.mu n (k n + 1) * sys.r (some n) (some m) *
              (w sys (Function.update k' n (k n + 1)) * W sys (S k))
              = (sys.mu n (k n + 1) * w sys (Function.update k' n (k n + 1))) *
                  sys.r (some n) (some m) * W sys (S k) := by ring
          _ = (sys.e n * w sys k') * sys.r (some n) (some m) * W sys (S k) := by rw [hw]
          _ = sys.e n * sys.r (some n) (some m) * w sys k' * W sys (S k) := by ring
      · simp [hmn]
    · simp [hm]
  -- Rewrite the service-outflow part of Term 1 using w_update_pred
  have hterm1b :
      (∑ m, sys.mu m (k m) * (1 - sys.r (some m) (some m))) * (w sys k * W sys (S k)) =
      (∑ m, if 0 < k m then
        sys.e m * (1 - sys.r (some m) (some m)) * w sys (Function.update k m (k m - 1))
        else 0) * W sys (S k) := by
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases hm : 0 < k m
    · rw [if_pos hm]
      have hw := w_update_pred sys k m hm
      calc
        sys.mu m (k m) * (1 - sys.r (some m) (some m)) * (w sys k * W sys (S k))
            = (sys.mu m (k m) * w sys k) * (1 - sys.r (some m) (some m)) * W sys (S k) := by ring
        _ = (sys.e m * w sys (Function.update k m (k m - 1))) *
              (1 - sys.r (some m) (some m)) * W sys (S k) := by rw [hw]
        _ = sys.e m * (1 - sys.r (some m) (some m)) *
              w sys (Function.update k m (k m - 1)) * W sys (S k) := by ring
    · have hk0 : k m = 0 := by omega
      rw [if_neg hm, hk0, sys.mu_zero]
      ring
  -- Combine Terms 2, 4, and 1b via e_traffic
  have hcomb :
      -(∑ m, if 0 < k m then
          sys.e m * (1 - sys.r (some m) (some m)) * w sys (Function.update k m (k m - 1))
          else 0)
      + (∑ m, if 0 < k m then sys.r none (some m) * w sys (Function.update k m (k m - 1)) else 0)
      + (∑ m, if 0 < k m then
          (∑ n, if m ≠ n then sys.e n * sys.r (some n) (some m) else 0) *
            w sys (Function.update k m (k m - 1))
          else 0) = 0 := by
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun m _ => ?_
    by_cases hm : 0 < k m
    · rw [if_pos hm, if_pos hm, if_pos hm]
      have hdiag :
          sys.e m * sys.r (some m) (some m) +
            ∑ n, (if m ≠ n then sys.e n * sys.r (some n) (some m) else 0) =
          ∑ n, sys.e n * sys.r (some n) (some m) := by
        rw [← Finset.add_sum_erase _ (fun n => sys.e n * sys.r (some n) (some m))
              (Finset.mem_univ m)]
        congr 1
        rw [← Finset.add_sum_erase _ (fun n => if m ≠ n then sys.e n * sys.r (some n) (some m) else 0)
              (Finset.mem_univ m)]
        simp only [ne_eq, not_true_eq_false, ↓reduceIte, zero_add]
        exact Finset.sum_congr rfl fun n hn => by
          rw [if_pos (Ne.symm (Finset.ne_of_mem_erase hn))]
      have htraf := sys.e_traffic m
      have hcoeff :
          -(sys.e m * (1 - sys.r (some m) (some m))) + sys.r none (some m) +
            ∑ n, (if m ≠ n then sys.e n * sys.r (some n) (some m) else 0) = 0 := by
        linarith
      calc
        -(sys.e m * (1 - sys.r (some m) (some m)) * w sys (Function.update k m (k m - 1))) +
            sys.r none (some m) * w sys (Function.update k m (k m - 1)) +
            (∑ n, if m ≠ n then sys.e n * sys.r (some n) (some m) else 0) *
              w sys (Function.update k m (k m - 1))
            = (-(sys.e m * (1 - sys.r (some m) (some m))) + sys.r none (some m) +
                ∑ n, (if m ≠ n then sys.e n * sys.r (some n) (some m) else 0)) *
                w sys (Function.update k m (k m - 1)) := by ring
        _ = 0 * w sys (Function.update k m (k m - 1)) := by rw [hcoeff]
        _ = 0 := zero_mul _
    · simp [hm]
  rw [hterm2, hterm3, hterm4]
  have h1 :
      -((sys.lam (S k) * ∑ n, sys.r none (some n)) +
          ∑ n, sys.mu n (k n) * (1 - sys.r (some n) (some n))) *
        (w sys k * W sys (S k)) =
      -(sys.lam (S k) * (∑ n, sys.r none (some n)) * (w sys k * W sys (S k))) -
        (∑ m, sys.mu m (k m) * (1 - sys.r (some m) (some m))) * (w sys k * W sys (S k)) := by
    ring
  rw [h1, hterm1b]
  have hcomb' := congrArg (· * W sys (S k)) hcomb
  simp only [zero_mul] at hcomb'
  linarith

private lemma balance_smul {N : ℕ} (sys : JobshopSystem N) (c : ℝ)
    (q : (Fin N → ℕ) → ℝ) (k : Fin N → ℕ) (hq : Balance sys q k) :
    Balance sys (fun x => c * q x) k := by
  unfold Balance at hq ⊢
  have h :
      -((sys.lam (S k) * ∑ n, sys.r none (some n)) +
          ∑ n, sys.mu n (k n) * (1 - sys.r (some n) (some n))) * (c * q k)
      + ∑ n, (if 0 < k n then
          sys.lam (S k - 1) * sys.r none (some n) * (c * q (Function.update k n (k n - 1))) else 0)
      + ∑ n, sys.mu n (k n + 1) * sys.r (some n) none * (c * q (Function.update k n (k n + 1)))
      + ∑ m, ∑ n, (if m ≠ n ∧ 0 < k m then
          sys.mu n (k n + 1) * sys.r (some n) (some m) *
            (c * q (Function.update (Function.update k m (k m - 1)) n (k n + 1))) else 0) =
      c * (-((sys.lam (S k) * ∑ n, sys.r none (some n)) +
              ∑ n, sys.mu n (k n) * (1 - sys.r (some n) (some n))) * q k
        + ∑ n, (if 0 < k n then
            sys.lam (S k - 1) * sys.r none (some n) * q (Function.update k n (k n - 1)) else 0)
        + ∑ n, sys.mu n (k n + 1) * sys.r (some n) none * q (Function.update k n (k n + 1))
        + ∑ m, ∑ n, (if m ≠ n ∧ 0 < k m then
            sys.mu n (k n + 1) * sys.r (some n) (some m) *
              q (Function.update (Function.update k m (k m - 1)) n (k n + 1)) else 0)) := by
    have h2 :
        ∑ n, (if 0 < k n then
            sys.lam (S k - 1) * sys.r none (some n) * (c * q (Function.update k n (k n - 1)))
            else 0) =
        c * ∑ n, (if 0 < k n then
            sys.lam (S k - 1) * sys.r none (some n) * q (Function.update k n (k n - 1))
            else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      split_ifs <;> ring
    have h3 :
        ∑ n, sys.mu n (k n + 1) * sys.r (some n) none * (c * q (Function.update k n (k n + 1))) =
        c * ∑ n, sys.mu n (k n + 1) * sys.r (some n) none * q (Function.update k n (k n + 1)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => by ring
    have h4 :
        ∑ m, ∑ n, (if m ≠ n ∧ 0 < k m then
            sys.mu n (k n + 1) * sys.r (some n) (some m) *
              (c * q (Function.update (Function.update k m (k m - 1)) n (k n + 1))) else 0) =
        c * ∑ m, ∑ n, (if m ≠ n ∧ 0 < k m then
            sys.mu n (k n + 1) * sys.r (some n) (some m) *
              q (Function.update (Function.update k m (k m - 1)) n (k n + 1)) else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      split_ifs <;> ring
    rw [h2, h3, h4]
    ring
  rw [h, ← hq, mul_zero]

end JacksonJobshop.Equilibrium

open JacksonJobshop.Equilibrium in
theorem solution {N : ℕ} (sys : JobshopSystem N) :
    ∀ k, Balance sys (productForm sys) k := by
  intro k
  have h : productForm sys = fun x => piConst sys * (w sys x * W sys (S x)) := by
    ext x
    unfold productForm
    ring
  rw [h]
  exact balance_smul sys (piConst sys) (fun x => w sys x * W sys (S x)) k (balance_unscaled sys k)
