-- Prove2me | solution 1 for KellyStochasticNetworks.FlowStability.supporting_utility
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:06:56.411243+00:00
-- url     : https://prove2.me/submissions/91a7d1f5-42e9-4322-b22b-ab0bf8bc65ce

import Mathlib
import Definitions.Def_KellyStochasticNetworks_FlowStability_Network

open KellyStochasticNetworks.FlowStability

/-- tangent inequality for `x ↦ x^q/q` -/
theorem g78k_tan (q : ℝ) (hq0 : q ≠ 0) (hq1 : q < 1) (t : ℝ) (ht : 0 < t) :
    (t ^ q - 1) / q ≤ t - 1 := by
  rcases lt_or_gt_of_ne hq0 with hneg | hpos
  · -- q < 0: show t^q - 1 ≥ q (t - 1)
    set p := -q with hp
    have hp0 : 0 < p := by linarith
    have key : 1 + q * (t - 1) ≤ t ^ q := by
      rcases le_total p 1 with hp1 | hp1
      · have hb := rpow_one_add_le_one_add_mul_self (s := t - 1) (by linarith) hp0.le hp1
        rw [show 1 + (t - 1) = t by ring] at hb
        have hy : 0 < 1 + p * (t - 1) := by nlinarith
        have htp : 0 < t ^ p := Real.rpow_pos_of_pos ht p
        rw [show q = -p by linarith, Real.rpow_neg ht.le]
        have h1 : (1 + p * (t - 1))⁻¹ ≤ (t ^ p)⁻¹ := inv_anti₀ htp hb
        have h2 : 1 - p * (t - 1) ≤ (1 + p * (t - 1))⁻¹ := by
          set y := p * (t - 1)
          have e : (1 + y)⁻¹ = (1 - y) + y ^ 2 / (1 + y) := by field_simp; ring
          rw [e]
          have := div_nonneg (sq_nonneg y) hy.le
          linarith
        linarith
      · have hb := one_add_mul_self_le_rpow_one_add (s := t⁻¹ - 1)
          (by have := inv_pos.2 ht; linarith) hp1
        rw [show 1 + (t⁻¹ - 1) = t⁻¹ by ring, Real.inv_rpow ht.le] at hb
        rw [show q = -p by linarith, Real.rpow_neg ht.le]
        have h3 : t⁻¹ - 1 ≥ 1 - t := by
          have : t⁻¹ + t ≥ 2 := by
            rw [ge_iff_le, ← sub_nonneg]
            have : t⁻¹ + t - 2 = (t - 1) ^ 2 / t := by field_simp; ring
            rw [this]; positivity
          linarith
        nlinarith
    rw [div_le_iff_of_neg hneg]
    nlinarith
  · have hb := rpow_one_add_le_one_add_mul_self (s := t - 1) (by linarith) hpos.le hq1.le
    rw [show 1 + (t - 1) = t by ring] at hb
    rw [div_le_iff₀ hpos]
    nlinarith

theorem solution {J R : ℕ} (D : Network J R)
    (X : State R → Fin R → ℝ) (hX : IsAlphaFair D X)
    (n : State R) (U : Fin R → ℝ)
    (hU : U ∈ KellyStochasticNetworks.networkFeasible D.A D.C)
    (hUpos : ∀ r, 0 < n r → 0 < U r) :
    (∑ r ∈ Finset.univ.filter (fun r => 0 < n r),
      D.w r * (n r : ℝ) ^ D.alpha * U r ^ (-D.alpha) * (U r - X n r))
      ≤ aggregateUtility D n U - aggregateUtility D n (X n) ∧
    aggregateUtility D n U - aggregateUtility D n (X n) ≤ 0 := by
  have ha := D.alpha_pos
  have hXa := (hX n).1
  have hXpos : ∀ r, 0 < n r → 0 < X n r := hXa.2.2
  -- per-route utility
  set T : ℕ → ℝ → ℝ := fun k v => if D.alpha = 1 then (k : ℝ) * Real.log v
    else (k : ℝ) ^ D.alpha * (v ^ (1 - D.alpha) / (1 - D.alpha)) with hT
  have hagg : ∀ V : Fin R → ℝ, aggregateUtility D n V = ∑ r, D.w r * T (n r) (V r) := by
    intro V
    simp only [aggregateUtility, KellyStochasticNetworks.alphaFairObjective, hT]
    split_ifs with h1
    · exact Finset.sum_congr rfl fun r _ => by ring
    · exact Finset.sum_congr rfl fun r _ => by ring
  have hT0 : ∀ v, T 0 v = 0 := by
    intro v; simp only [hT, Nat.cast_zero]
    split_ifs
    · simp
    · rw [Real.zero_rpow ha.ne', zero_mul]
  -- part 2
  have part2 : aggregateUtility D n U - aggregateUtility D n (X n) ≤ 0 := by
    set U' : Fin R → ℝ := fun r => if 0 < n r then U r else 0
    have hU' : U' ∈ activeFeasible D n := by
      refine ⟨⟨fun r => ?_, fun j => ?_⟩, fun r hr => ?_, fun r hr => ?_⟩
      · simp only [U']; split_ifs
        · exact hU.1 r
        · exact le_rfl
      · refine le_trans ?_ (hU.2 j)
        simp only [KellyStochasticNetworks.linkFlow]
        refine Finset.sum_le_sum fun r _ => ?_
        have hA : 0 ≤ D.A j r := by rcases D.incidence j r with h | h <;> rw [h] <;> norm_num
        simp only [U']; split_ifs
        · exact le_rfl
        · rw [mul_zero]; exact mul_nonneg hA (hU.1 r)
      · simp [U', hr]
      · simp only [U', if_pos hr]; exact hUpos r hr
    have heq : aggregateUtility D n U = aggregateUtility D n U' := by
      rw [hagg, hagg]
      refine Finset.sum_congr rfl fun r _ => ?_
      by_cases hr : 0 < n r
      · simp [U', hr]
      · have : n r = 0 := by omega
        rw [this, hT0, hT0]
    rw [heq]
    linarith [(hX n).2 U' hU']
  refine ⟨?_, part2⟩
  rw [hagg, hagg, ← Finset.sum_sub_distrib, ← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun r => 0 < n r)]
  have hzero : ∑ r ∈ Finset.univ.filter (fun r => ¬ 0 < n r),
      (D.w r * T (n r) (U r) - D.w r * T (n r) (X n r)) = 0 := by
    refine Finset.sum_eq_zero fun r hr => ?_
    have : n r = 0 := by simp at hr; omega
    rw [this, hT0, hT0]; ring
  rw [hzero, add_zero]
  refine Finset.sum_le_sum fun r hr => ?_
  have hn : 0 < n r := (Finset.mem_filter.1 hr).2
  have hu := hUpos r hn
  have hx := hXpos r hn
  have hw := D.weight_pos r
  have hnr : (0 : ℝ) < n r := by exact_mod_cast hn
  simp only [hT]
  split_ifs with h1
  · -- logarithmic case
    rw [h1, Real.rpow_one, Real.rpow_neg_one]
    have hlog : (U r - X n r) / U r ≤ Real.log (U r) - Real.log (X n r) := by
      have := Real.log_le_sub_one_of_pos (div_pos hx hu)
      rw [Real.log_div hx.ne' hu.ne'] at this
      have e : (U r - X n r) / U r = 1 - X n r / U r := by field_simp
      linarith
    have hwn : 0 < D.w r * (n r : ℝ) := mul_pos hw hnr
    calc D.w r * (n r : ℝ) * (U r)⁻¹ * (U r - X n r) = D.w r * (n r : ℝ) * ((U r - X n r) / U r) := by
          field_simp
      _ ≤ D.w r * (n r : ℝ) * (Real.log (U r) - Real.log (X n r)) :=
          mul_le_mul_of_nonneg_left hlog hwn.le
      _ = _ := by ring
  · set q := 1 - D.alpha with hq
    have hq0 : q ≠ 0 := by intro h; apply h1; linarith
    have hq1 : q < 1 := by linarith
    set t := X n r / U r with htdef
    have ht : 0 < t := div_pos hx hu
    have hX' : X n r = U r * t := by rw [htdef]; field_simp
    have hXq : X n r ^ q = U r ^ q * t ^ q := by rw [hX', Real.mul_rpow hu.le ht.le]
    have hUa : U r ^ (-D.alpha) * U r = U r ^ q := by
      rw [hq, show (1 : ℝ) - D.alpha = -D.alpha + 1 by ring, Real.rpow_add hu, Real.rpow_one]
    have hUq : 0 < U r ^ q := Real.rpow_pos_of_pos hu q
    have hc : 0 < D.w r * (n r : ℝ) ^ D.alpha * U r ^ q :=
      mul_pos (mul_pos hw (Real.rpow_pos_of_pos hnr _)) hUq
    have htan := g78k_tan q hq0 hq1 t ht
    have lhs : D.w r * (n r : ℝ) ^ D.alpha * U r ^ (-D.alpha) * (U r - X n r) =
        D.w r * (n r : ℝ) ^ D.alpha * U r ^ q * (1 - t) := by
      rw [← hUa, hX']; ring
    have rhs : D.w r * ((n r : ℝ) ^ D.alpha * (U r ^ q / q)) -
        D.w r * ((n r : ℝ) ^ D.alpha * (X n r ^ q / q)) =
        D.w r * (n r : ℝ) ^ D.alpha * U r ^ q * ((1 - t ^ q) / q) := by
      rw [hXq]; field_simp
    rw [lhs, rhs]
    refine mul_le_mul_of_nonneg_left ?_ hc.le
    have : (1 - t ^ q) / q = -((t ^ q - 1) / q) := by ring
    linarith
