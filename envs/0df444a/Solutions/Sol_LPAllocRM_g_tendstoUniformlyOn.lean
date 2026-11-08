-- Prove2me | solution 1 for LPAllocRM.g_tendstoUniformlyOn
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T00:50:32.689998+00:00
-- url     : https://prove2.me/submissions/2daf88ea-ba51-4c2d-bc36-90086b2cef38

import Mathlib
open Filter

theorem solution {n : ℕ} (f : Fin n → ℝ) (xstar : Fin n → ℝ) :
    Continuous (fun y : Fin n → ℝ => ∑ j, f j * min (y j) (xstar j)) ∧
      ∀ K : Set (Fin n → ℝ), IsCompact K →
        TendstoUniformlyOn
          (fun (k : ℕ+) (y : Fin n → ℝ) =>
            ∑ j, f j * min (y j) (((k : ℕ) : ℝ)⁻¹ * (⌊((k : ℕ) : ℝ) * xstar j⌋ : ℝ)))
          (fun y : Fin n → ℝ => ∑ j, f j * min (y j) (xstar j)) atTop K := by
  refine ⟨continuous_finsetSum _ fun j _ =>
    continuous_const.mul ((continuous_apply j).min continuous_const), fun K _ => ?_⟩
  have hround : ∀ (k : ℕ+) (x : ℝ),
      |((k : ℕ) : ℝ)⁻¹ * (⌊((k : ℕ) : ℝ) * x⌋ : ℝ) - x| ≤ ((k : ℕ) : ℝ)⁻¹ := by
    intro k x
    have hk : (0 : ℝ) < ((k : ℕ) : ℝ) := by exact_mod_cast k.pos
    have h1 := Int.floor_le (((k : ℕ) : ℝ) * x)
    have h2 := Int.lt_floor_add_one (((k : ℕ) : ℝ) * x)
    have e : ((k : ℕ) : ℝ)⁻¹ * (⌊((k : ℕ) : ℝ) * x⌋ : ℝ) - x =
        ((k : ℕ) : ℝ)⁻¹ * ((⌊((k : ℕ) : ℝ) * x⌋ : ℝ) - ((k : ℕ) : ℝ) * x) := by
      rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hk.ne', one_mul]
    rw [e, abs_mul, abs_of_pos (inv_pos.mpr hk)]
    apply mul_le_of_le_one_right (inv_nonneg.mpr hk.le)
    rw [abs_le]; constructor <;> linarith
  obtain ⟨S, hSd⟩ : ∃ S, S = ∑ j, |f j| := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hSd]; exact Finset.sum_nonneg fun j _ => abs_nonneg _
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (S / ε)
  rw [Filter.eventually_atTop]
  refine ⟨⟨N + 1, Nat.succ_pos N⟩, fun k hk y _ => ?_⟩
  have hkN : ((N : ℝ) + 1) ≤ ((k : ℕ) : ℝ) := by
    have : N + 1 ≤ (k : ℕ) := hk
    exact_mod_cast this
  have hkpos : (0 : ℝ) < ((k : ℕ) : ℝ) := by exact_mod_cast k.pos
  rw [Real.dist_eq, ← Finset.sum_sub_distrib]
  calc |∑ j, (f j * min (y j) (xstar j) -
          f j * min (y j) (((k : ℕ) : ℝ)⁻¹ * (⌊((k : ℕ) : ℝ) * xstar j⌋ : ℝ)))|
      ≤ ∑ j, |f j * min (y j) (xstar j) -
          f j * min (y j) (((k : ℕ) : ℝ)⁻¹ * (⌊((k : ℕ) : ℝ) * xstar j⌋ : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |f j| * ((k : ℕ) : ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro j _
        rw [← mul_sub, abs_mul]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        have hm := abs_min_sub_min_le_max (y j) (xstar j) (y j)
          (((k : ℕ) : ℝ)⁻¹ * (⌊((k : ℕ) : ℝ) * xstar j⌋ : ℝ))
        rw [sub_self, abs_zero, max_eq_right (abs_nonneg _), abs_sub_comm (xstar j)] at hm
        exact le_trans hm (hround k (xstar j))
    _ = S * ((k : ℕ) : ℝ)⁻¹ := by rw [← Finset.sum_mul, hSd]
    _ < ε := by
        rw [← div_eq_mul_inv, div_lt_iff₀ hkpos]
        rw [div_lt_iff₀ hε] at hN
        nlinarith
