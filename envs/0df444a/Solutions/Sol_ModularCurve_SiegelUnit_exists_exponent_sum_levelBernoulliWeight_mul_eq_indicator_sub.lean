-- Prove2me | solution 1 for ModularCurve.SiegelUnit.exists_exponent_sum_levelBernoulliWeight_mul_eq_indicator_sub
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/68e83755-5410-5f44-95d7-2db83990a7b8

import Mathlib
import Theorems.Thm_ModularCurve_SiegelUnit_mem_span_levelBernoulliWeight_dilate_iff_even
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_SiegelUnit_exists_exponent_sum_levelBernoulliWeight_mul_eq_indicator_sub

set_option autoImplicit false

namespace HSEPR1

theorem sum_range_weight_aux (n m : ℕ) :
    ∑ t ∈ Finset.range m, (6 * (t : ℤ) ^ 2 - 6 * (n : ℤ) * (t : ℤ) + (n : ℤ) ^ 2) =
      (m : ℤ) * ((m : ℤ) - 1) * (2 * (m : ℤ) - 1) - 3 * (n : ℤ) * (m : ℤ) * ((m : ℤ) - 1) + (m : ℤ) * (n : ℤ) ^ 2 := by
  induction m with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem sum_range_weight (n : ℕ) :
    ∑ t ∈ Finset.range n, (6 * (t : ℤ) ^ 2 - 6 * (n : ℤ) * (t : ℤ) + (n : ℤ) ^ 2) = (n : ℤ) := by
  rw [sum_range_weight_aux]; ring

theorem sum_zmod_weight (n : ℕ) :
    ∑ t : ZMod (n + 1), (6 * ((t.val : ℕ) : ℤ) ^ 2 - 6 * ((n + 1 : ℕ) : ℤ) * ((t.val : ℕ) : ℤ) + ((n + 1 : ℕ) : ℤ) ^ 2) =
      ((n + 1 : ℕ) : ℤ) := by
  have h := Fin.sum_univ_eq_sum_range
    (fun t : ℕ => (6 * (t : ℤ) ^ 2 - 6 * ((n + 1 : ℕ) : ℤ) * (t : ℤ) + ((n + 1 : ℕ) : ℤ) ^ 2)) (n + 1)
  rw [sum_range_weight (n + 1)] at h
  exact h

end HSEPR1

namespace HSEPR1

def W (q : ℕ) (t : ZMod q) : ℤ := 6 * ((t.val : ℕ) : ℤ) ^ 2 - 6 * (q : ℤ) * ((t.val : ℕ) : ℤ) + (q : ℤ) ^ 2

theorem W_zero (q : ℕ) [NeZero q] : W q 0 = (q : ℤ) ^ 2 := by
  simp [W, ZMod.val_zero]

theorem sum_W (q : ℕ) [NeZero q] : ∑ t : ZMod q, W q t = (q : ℤ) := by
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (NeZero.ne q))).symm⟩
  exact sum_zmod_weight n

theorem sum_W_mul (q : ℕ) [Fact q.Prime] (x : ZMod q) (hx : x ≠ 0) : ∑ s : ZMod q, W q (s * x) = (q : ℤ) := by
  rw [← sum_W q]
  exact Fintype.sum_equiv (Equiv.mulRight₀ x hx) _ _ (fun s => rfl)

theorem sum_W_mul_ne_zero (q : ℕ) [Fact q.Prime] (x : ZMod q) (hx : x ≠ 0) :
    ∑ s : ZMod q, (if s = 0 then 0 else W q (s * x)) = (q : ℤ) - (q : ℤ) ^ 2 := by
  classical
  have h1 : ∑ s : ZMod q, (if s = 0 then 0 else W q (s * x)) = ∑ s ∈ Finset.univ.erase (0 : ZMod q), W q (s * x) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod q)), if_pos rfl, add_zero]
    exact Finset.sum_congr rfl (fun s hs => if_neg (Finset.ne_of_mem_erase hs))
  have h2 := sum_W_mul q x hx
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod q)), zero_mul, W_zero] at h2
  rw [h1]
  linear_combination h2

end HSEPR1

open HSEPR1 in

theorem solution
    (q : ℕ) [Fact q.Prime] :
    ∃ (μ : ZMod q → ℕ) (t e : ℕ), μ 0 = 0 ∧ 0 < e ∧
      ∀ x : ZMod q, x ≠ 0 →
        ∑ r : ZMod q, (μ r : ℤ) *
            (6 * (((r * x).val : ℕ) : ℤ) ^ 2 - 6 * (q : ℤ) * (((r * x).val : ℕ) : ℤ) + (q : ℤ) ^ 2) =
          (if x = 1 ∨ x = -1 then (e : ℤ) else 0) - (t : ℤ) := by
  classical
  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le
  have hqq : (q : ℚ) - (q : ℚ) ^ 2 ≠ 0 := by
    intro h
    have h2 : (q : ℚ) * ((q : ℚ) - 1) = 0 := by linear_combination (-1 : ℚ) * h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd (by exact_mod_cast h3 : q = 0) (by omega)
    · have : (q : ℚ) = 1 := by linear_combination h3
      exact absurd (by exact_mod_cast this : q = 1) (by omega)

  set φ : ZMod q → ℚ := fun r => if r = 1 ∨ r = -1 then 1 else 0 with hφ
  have hφeven : ∀ r : ZMod q, φ (-r) = φ r := by
    intro r
    simp only [hφ, neg_eq_iff_eq_neg, neg_neg, or_comm]
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp
    ((ModularCurve.SiegelUnit.mem_span_levelBernoulliWeight_dilate_iff_even q φ).mpr hφeven)
  have hc' : ∀ r : ZMod q, ∑ s : ZMod q, c s * (W q (s * r) : ℚ) = φ r := by
    intro r
    have := congrFun hc r
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, W] using this

  set κ : ℚ := c 0 * (q : ℚ) ^ 2 / ((q : ℚ) - (q : ℚ) ^ 2) with hκ
  have hκ' : κ * ((q : ℚ) - (q : ℚ) ^ 2) = c 0 * (q : ℚ) ^ 2 := by rw [hκ, div_mul_cancel₀ _ hqq]
  set c' : ZMod q → ℚ := fun s => if s = 0 then 0 else c s + κ with hc'def
  have hW0 : (W q 0 : ℚ) = (q : ℚ) ^ 2 := by rw [W_zero]; push_cast; ring
  have hsumW : ∀ r : ZMod q, r ≠ 0 → ∑ s : ZMod q, (W q (s * r) : ℚ) = q := fun r hr => by
    exact_mod_cast sum_W_mul q r hr
  have hc'' : ∀ r : ZMod q, r ≠ 0 → ∑ s : ZMod q, c' s * (W q (s * r) : ℚ) = φ r := by
    intro r hr
    have h1 : ∑ s : ZMod q, c' s * (W q (s * r) : ℚ) =
        ∑ s : ZMod q, (c s + κ) * (W q (s * r) : ℚ) - (c 0 + κ) * (W q 0 : ℚ) := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod q)),
        ← Finset.sum_erase_add (Finset.univ) (fun s => (c s + κ) * (W q (s * r) : ℚ)) (Finset.mem_univ (0 : ZMod q))]
      simp only [hc'def, if_pos rfl, zero_mul, add_zero, zero_mul]
      rw [add_sub_cancel_right]
      refine Finset.sum_congr rfl (fun s hs => ?_)
      rw [if_neg (Finset.ne_of_mem_erase hs)]
    rw [h1, Finset.sum_congr rfl (fun s _ => add_mul (c s) κ (W q (s * r) : ℚ)), Finset.sum_add_distrib, hc' r,
      ← Finset.mul_sum, hsumW r hr, hW0]
    linear_combination hκ'

  set D : ℕ := ∏ s : ZMod q, (c' s).den with hD
  have hDpos : 0 < D := Finset.prod_pos (fun s _ => (c' s).den_pos)
  have hz : ∀ s : ZMod q, ∃ z : ℤ, (z : ℚ) = (D : ℚ) * c' s := by
    intro s
    obtain ⟨k, hk⟩ : (c' s).den ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ s)
    refine ⟨(k : ℤ) * (c' s).num, ?_⟩
    rw [hk]
    push_cast
    rw [mul_comm ((c' s).den : ℚ) (k : ℚ), mul_assoc, Rat.den_mul_eq_num]
  choose z hz using hz
  have hz0 : z 0 = 0 := by
    have : (z 0 : ℚ) = 0 := by rw [hz, hc'def]; simp
    exact_mod_cast this
  set Λ : ℤ := ∑ s : ZMod q, |z s| with hΛ
  have hΛ0 : 0 ≤ Λ := Finset.sum_nonneg (fun s _ => abs_nonneg (z s))
  have hΛ' : ∀ s : ZMod q, 0 ≤ z s + Λ := by
    intro s
    have h1 : |z s| ≤ Λ := Finset.single_le_sum (f := fun s => |z s|) (fun _ _ => abs_nonneg _) (Finset.mem_univ s)
    have h2 := neg_abs_le (z s)
    omega
  set μ : ZMod q → ℕ := fun s => if s = 0 then 0 else (z s + Λ).toNat with hμdef
  have hμ : ∀ r : ZMod q, (μ r : ℤ) = if r = 0 then 0 else z r + Λ := by
    intro r
    by_cases hr : r = 0
    · simp [hμdef, hr]
    · simp [hμdef, hr, Int.toNat_of_nonneg (hΛ' r)]
  refine ⟨μ, Λ.toNat * (q ^ 2 - q), D, by simp [hμdef], hDpos, ?_⟩
  intro x hx

  have hzsum : ((∑ r : ZMod q, z r * W q (r * x) : ℤ) : ℚ) = (D : ℚ) * φ x := by
    push_cast
    rw [Finset.sum_congr rfl (fun r _ => by rw [hz r]), Finset.sum_congr rfl (fun r _ => mul_assoc (D : ℚ) (c' r) (W q (r * x) : ℚ)),
      ← Finset.mul_sum, hc'' x hx]
  have hzsumZ : ∑ r : ZMod q, z r * W q (r * x) = if x = 1 ∨ x = -1 then (D : ℤ) else 0 := by
    have : ((∑ r : ZMod q, z r * W q (r * x) : ℤ) : ℚ) = ((if x = 1 ∨ x = -1 then (D : ℤ) else 0 : ℤ) : ℚ) := by
      rw [hzsum]
      by_cases hx1 : x = 1 ∨ x = -1
      · simp [hφ, hx1]
      · simp [hφ, hx1]
    exact_mod_cast this

  have hsplit : ∀ r : ZMod q, (μ r : ℤ) * W q (r * x) =
      z r * W q (r * x) + Λ * (if r = 0 then 0 else W q (r * x)) := by
    intro r
    rw [hμ r]
    by_cases hr : r = 0
    · rw [if_pos hr, if_pos hr, hr, hz0]; ring
    · rw [if_neg hr, if_neg hr]; ring
  have hmain : ∑ r : ZMod q, (μ r : ℤ) * W q (r * x) =
      (if x = 1 ∨ x = -1 then (D : ℤ) else 0) + Λ * ((q : ℤ) - (q : ℤ) ^ 2) := by
    rw [Finset.sum_congr rfl (fun r _ => hsplit r), Finset.sum_add_distrib, hzsumZ, ← Finset.mul_sum,
      sum_W_mul_ne_zero q x hx]
  have hcast1 : ((Λ.toNat * (q ^ 2 - q) : ℕ) : ℤ) = Λ * ((q : ℤ) ^ 2 - (q : ℤ)) := by
    push_cast
    rw [Int.toNat_of_nonneg hΛ0, Nat.cast_sub (by nlinarith), Nat.cast_pow]
  simp only [W] at hmain
  rw [hmain, hcast1]
  ring

end S_ModularCurve_SiegelUnit_exists_exponent_sum_levelBernoulliWeight_mul_eq_indicator_sub
end P2MW
export P2MW.S_ModularCurve_SiegelUnit_exists_exponent_sum_levelBernoulliWeight_mul_eq_indicator_sub (solution)
