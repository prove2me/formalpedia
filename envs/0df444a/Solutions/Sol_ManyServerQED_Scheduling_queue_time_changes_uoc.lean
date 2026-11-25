-- Prove2me | solution 1 for ManyServerQED.Scheduling.queue_time_changes_uoc
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T19:22:35.245794+00:00
-- url     : https://prove2.me/submissions/dc715b69-2cd4-43ad-99ee-4b99783a0e88

import Theorems.Thm_ManyServerQED_Scheduling_controlled_compact_containment

open MeasureTheory Filter Topology Set
open scoped ENNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

private theorem interval_abs_const_bound {f : ℝ → ℝ} {s L : ℝ} (hs : 0 ≤ s)
    (hF : IntervalIntegrable f volume 0 s) (hL : ∀ t ∈ Icc 0 s, |f t| ≤ L) :
    |∫ r in (0 : ℝ)..s, f r| ≤ s * L := by
  have hmono := intervalIntegral.integral_mono_on hs hF.abs
    (intervalIntegrable_const (c := L)) hL
  have h := intervalIntegral.abs_integral_le_integral_abs (μ := volume) (f := f) hs
  exact h.trans (by simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] using hmono)

private theorem clock_coordinate_bounds {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (hn : 0 < n)
    (X0 : Fin k → ℕ) (X Ψ : Ω → ℝ → Fin k → ℝ)
    (hC : M.IsControlled n X0 X Ψ) (hWork : IsWorkConserving n X Ψ)
    (ω : Ω) (T B : ℝ) (hB : 0 ≤ B)
    (hX : ∀ t ∈ Icc 0 T, ‖M.Xhat n X ω t‖ ≤ B)
    (s : ℝ) (hs : s ∈ Icc 0 T) (i : Fin k) :
    |busyTime Ψ ω i s / (n : ℝ) - M.rho i * s| ≤
        ((k : ℝ) + 1) * B * T / Real.sqrt n ∧
      |queueTime X Ψ ω i s / (n : ℝ)| ≤ ((k : ℝ) + 1) * B * T / Real.sqrt n := by
  let r := Real.sqrt (n : ℝ)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : 0 < r := Real.sqrt_pos.2 hnR
  have hr2 : r ^ 2 = (n : ℝ) := Real.sq_sqrt hnR.le
  let x (t : ℝ) := M.Xhat n X ω t
  let q (t : ℝ) := Phihat n X Ψ ω t
  let p (t : ℝ) := M.Psihat n Ψ ω t
  have hpq (t : ℝ) (j : Fin k) : p t j = x t j - q t j := by
    unfold p x q SystemSequence.Xhat SystemSequence.Psihat Phihat
    ring
  have hnQ (t : ℝ) (ht : 0 ≤ t) (j : Fin k) : 0 ≤ q t j :=
    div_nonneg (hC.phi_nonneg ω t j ht) hr.le
  have hSum (t : ℝ) (ht : 0 ≤ t) : (∑ j, q t j) = max (∑ j, x t j) 0 := by
    have hx : (∑ j, x t j) = ((∑ j, X ω t j) - n) / r := by
      simp only [x, SystemSequence.Xhat, ← Finset.sum_div, Finset.sum_sub_distrib,
        ← Finset.sum_mul, show (∑ j, M.rho j) = 1 from M.sum_rho, one_mul, r]
    simp only [q, Phihat, ← Finset.sum_div, ← hWork ω t ht]
    rw [← max_div_div_right (show 0 ≤ Real.sqrt (n : ℝ) from hr.le), zero_div, hx]
  have hq (t : ℝ) (ht : t ∈ Icc 0 T) (j : Fin k) : |q t j| ≤ (k : ℝ) * B := by
    rw [abs_of_nonneg (hnQ t ht.1 j)]
    refine (Finset.single_le_sum (fun l _ => hnQ t ht.1 l) (Finset.mem_univ j)).trans ?_
    rw [hSum t ht.1]
    refine max_le ?_ (mul_nonneg (Nat.cast_nonneg _) hB)
    calc
      ∑ j, x t j ≤ ∑ _ : Fin k, B :=
        Finset.sum_le_sum (fun i _ => le_trans (le_abs_self _) (by
          exact ((by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (x t) i :
            |x t i| ≤ ‖x t‖)).trans (hX t ht)))
      _ = (k : ℝ) * B := by simp
  have hpp (t : ℝ) (ht : t ∈ Icc 0 T) (j : Fin k) : |p t j| ≤ ((k : ℝ) + 1) * B := by
    rw [hpq]
    have hxj : |x t j| ≤ B := (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (x t) j :
      |x t j| ≤ ‖x t‖).trans (hX t ht)
    have hh := (abs_sub (x t j) (q t j)).trans (add_le_add hxj (hq t ht j))
    linarith
  have hpIn : IntervalIntegrable (fun t => p t i) volume 0 s :=
    ((hC.integrable ω i s hs.1).1.sub intervalIntegrable_const).div_const r
  have hqIn : IntervalIntegrable (fun t => q t i) volume 0 s :=
    (hC.integrable ω i s hs.1).2.div_const r
  have hpEq : (∫ t in (0 : ℝ)..s, p t i) / r = busyTime Ψ ω i s / (n : ℝ) - M.rho i * s := by
    unfold p SystemSequence.Psihat
    rw [intervalIntegral.integral_div, intervalIntegral.integral_sub (hC.integrable ω i s hs.1).1 intervalIntegrable_const]
    simp only [busyTime, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    change ((∫ t in (0 : ℝ)..s, Ψ ω t i) - s * (M.rho i * n)) / r / r = _
    rw [div_div, ← pow_two, hr2]
    field_simp
  have hqEq : (∫ t in (0 : ℝ)..s, q t i) / r = queueTime X Ψ ω i s / (n : ℝ) := by
    unfold q Phihat
    rw [intervalIntegral.integral_div, div_div]
    change queueTime X Ψ ω i s / (r * r) = _
    rw [← pow_two, hr2]
  have hIcc (t : ℝ) (ht : t ∈ Icc 0 s) : t ∈ Icc 0 T := ⟨ht.1, ht.2.trans hs.2⟩
  have hM : 0 ≤ ((k : ℝ) + 1) * B := mul_nonneg (by positivity) hB
  have hBound {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 s)
      (h : ∀ t ∈ Icc 0 s, |f t| ≤ ((k : ℝ) + 1) * B) :
      |(∫ t in (0 : ℝ)..s, f t) / r| ≤ ((k : ℝ) + 1) * B * T / r := by
    rw [abs_div, abs_of_nonneg hr.le]
    apply div_le_div_of_nonneg_right _ hr.le
    exact (interval_abs_const_bound hs.1 hf h).trans
      (by rw [mul_comm s]; exact mul_le_mul_of_nonneg_left hs.2 hM)
  constructor
  · rw [← hpEq]
    exact hBound hpIn (fun t ht => hpp t (hIcc t ht) i)
  · rw [← hqEq]
    exact hBound hqIn (fun t ht => (hq t (hIcc t ht) i).trans (by linarith))

theorem solution {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (X0 : ℕ → Fin k → ℕ) (x : Fin k → ℝ)
    (hX0 : Tendsto (fun n => M.Xhat0 n (X0 n)) atTop (𝓝 x))
    (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ)
    (hC : ∀ n, 1 ≤ n → M.IsControlled n (X0 n) (X n) (Ψ n))
    (hWork : ∀ n, 1 ≤ n → IsWorkConserving n (X n) (Ψ n)) :
    UocInProb M.P (fun n ω t i => busyTime (Ψ n) ω i t / (n : ℝ))
        (fun t i => M.rho i * t) ∧
      UocInProb M.P (fun n ω t i => queueTime (X n) (Ψ n) ω i t / (n : ℝ))
        (fun _ => 0) := by
  let C (queue : Bool) (n : ℕ) (ω : Ω) (t : ℝ) (i : Fin k) :=
    if queue then queueTime (X n) (Ψ n) ω i t / (n : ℝ) else busyTime (Ψ n) ω i t / (n : ℝ)
  let D (queue : Bool) (t : ℝ) (i : Fin k) := if queue then 0 else M.rho i * t
  have hCl (flag : Bool) : UocInProb M.P (C flag) (D flag) := by
    intro T hT ε hε
    refine tendsto_order.2 ⟨fun _ h => (not_lt_zero h).elim, fun η hη => ?_⟩
    have hq (n : ℕ) (hn : 1 ≤ n) (ω : Ω) (t : ℝ) (i : Fin k) (ht : 0 ≤ t) :
        X n ω t i - Ψ n ω t i ≤ max ((∑ j, X n ω t j) - n) 0 := by
      rw [hWork n hn ω t ht]
      exact Finset.single_le_sum (fun j _ => (hC n hn).phi_nonneg ω t j ht) (Finset.mem_univ i)
    obtain ⟨B, hB, hGood⟩ := controlled_compact_containment M X0 x hX0 X Ψ hC hq T hT η hη
    let b := (k : ℝ) * (((k : ℝ) + 1) * B * T)
    have hroot : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    have hsmall : Tendsto (fun n : ℕ => b / Real.sqrt n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hroot
    filter_upwards [hGood, (tendsto_order.1 hsmall).2 ε hε, eventually_ge_atTop (1 : ℕ)]
      with n hGood hnSmall hn
    refine lt_of_le_of_lt (measure_mono ?_) hGood
    intro ω hω
    by_contra h
    have hState (t : ℝ) (ht : t ∈ Icc 0 T) : ‖M.Xhat n (X n) ω t‖ ≤ B :=
      le_of_not_gt (fun hgt => h ⟨t, ht, hgt⟩)
    have hBound (t : ℝ) (ht : t ∈ Icc 0 T) (i : Fin k) :
        |C flag n ω t i - D flag t i| ≤ ((k : ℝ) + 1) * B * T / Real.sqrt n := by
      have hh := clock_coordinate_bounds M n hn (X0 n) (X n) (Ψ n) (hC n hn) (hWork n hn)
        ω T B hB hState t ht i
      cases flag
      · simpa only [C, D, Bool.false_eq_true, if_false] using hh.1
      · simpa only [C, D, if_true, sub_zero] using hh.2
    have hS : supDist (C flag n ω) (D flag) T ≤ ENNReal.ofReal (b / Real.sqrt n) := by
      unfold supDist
      refine iSup₂_le fun t ht => ENNReal.ofReal_le_ofReal ?_
      calc
        ∑ i, |C flag n ω t i - D flag t i| ≤ ∑ _ : Fin k, ((k : ℝ) + 1) * B * T / Real.sqrt n :=
          Finset.sum_le_sum (fun i _ => hBound t ht i)
        _ = b / Real.sqrt n := by simp [b, mul_div_assoc]
    exact (not_le_of_gt ((ENNReal.ofReal_lt_ofReal_iff hε).2 hnSmall)) (hω.trans hS)
  exact ⟨hCl false, hCl true⟩
