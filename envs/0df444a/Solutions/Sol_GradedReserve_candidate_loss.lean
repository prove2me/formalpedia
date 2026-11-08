-- Prove2me | solution 1 for GradedReserve.candidate_loss
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T02:23:32.373704+00:00
-- url     : https://prove2.me/submissions/74f1c399-5dc5-4bdc-b136-ad496f8fbe46

import Mathlib
import Definitions.Def_GradedReserve_Cfun__99e74d
import Definitions.Def_GradedReserve_cZero
import Definitions.Def_GradedReserve_pMin
import Definitions.Def_GradedReserve_powN
import Definitions.Def_GradedReserve_vbar
import Definitions.Def_GradedReserve_xStar
open MeasureTheory ProbabilityTheory Set Filter Topology

open GradedReserve in
theorem solution (k : ℝ) (hk : 1 ≤ k) (n : ℕ) (hn : 2 ≤ n) (p : ℝ) (hp : pMin k n < p) :
    Cfun k n (xStar k n p) =
      powN k n / (powN k n + 1) * (cZero k n p * vbar k n p) ^ (powN k n + 1)
        * (p / (p + powN k n + 1)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  set M := powM k n with hM
  set L := powL k n with hL
  set N := powN k n with hN
  have hLM : L = M + 1 := rfl
  have hM1 : 1 ≤ M := by
    rw [hM]; unfold powM; nlinarith
  have hL0 : 0 < L := by rw [hLM]; linarith
  have hN0 : 0 < N := by rw [hN]; unfold powN; nlinarith
  -- p is positive and above the root
  have hpmin0 : 0 ≤ pMin k n := by
    unfold pMin
    rw [← hL, ← hM]
    have : L ≤ Real.sqrt (L ^ 2 + 4 * k * M) := by
      rw [show L = Real.sqrt (L ^ 2) from (Real.sqrt_sq hL0.le).symm]
      apply Real.sqrt_le_sqrt
      rw [Real.sq_sqrt (by positivity)]
      nlinarith
    linarith
  have hp0 : 0 < p := lt_of_le_of_lt hpmin0 hp
  have hQ : k * M < p * (p + L) := by
    have h := hp
    unfold pMin at h
    rw [← hL, ← hM] at h
    have h2 : Real.sqrt (L ^ 2 + 4 * k * M) < 2 * p + L := by linarith
    have h3 : L ^ 2 + 4 * k * M < (2 * p + L) ^ 2 := by
      have hs := Real.sq_sqrt (show 0 ≤ L ^ 2 + 4 * k * M by positivity)
      have hsn := Real.sqrt_nonneg (L ^ 2 + 4 * k * M)
      nlinarith
    nlinarith
  -- positivity of vbar
  set V := vbar k n p with hV
  have hV0 : 0 < V := by
    rw [hV]
    unfold vbar
    rw [← hM, ← hL]
    apply Real.rpow_pos_of_pos
    apply mul_pos (by positivity)
    have : k * M / (p * (p + L)) < 1 := by
      rw [div_lt_one (by positivity)]; exact hQ
    linarith
  set c := cZero k n p with hc
  have hc0 : 0 < c := by
    rw [hc]; unfold cZero; rw [← hM, ← hL]; positivity
  have hcform : c = (M + p / (p + L)) / L := by
    rw [hc]; unfold cZero; rw [← hM, ← hL]
    field_simp
    rw [hLM]; ring
  set x := xStar k n p with hx
  have hxdef : ∀ t, x t = V ^ L * t ^ (L / p) := by intro t; rfl
  -- the Hardy average
  have hA : ∀ t, 0 < t → hardyAvg x t = x t * (p / (p + L)) := by
    intro t ht
    unfold hardyAvg
    have hint : ∫ u in (0 : ℝ)..t, x u = V ^ L * (t ^ (L / p + 1) / (L / p + 1)) := by
      simp only [hxdef]
      rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith [show (0:ℝ) < L / p by positivity]))]
      rw [Real.zero_rpow (by positivity), sub_zero]
    rw [hint, hxdef, Real.rpow_add_one ht.ne']
    field_simp <;> ring
  -- the bid
  have hbid : ∀ t, 0 < t → bidX k n (x t) (hardyAvg x t) = c * V * t ^ (1 / p) := by
    intro t ht
    have hxt : 0 < x t := by rw [hxdef]; positivity
    unfold bidX
    rw [if_neg hxt.ne', hA t ht, ← hM, ← hL]
    have hpow : x t / x t ^ (M / L) = V * t ^ (1 / p) := by
      rw [← Real.rpow_one_sub' hxt.le (by
        have : M / L < 1 := by rw [div_lt_one hL0]; linarith
        linarith)]
      have : 1 - M / L = 1 / L := by rw [hLM]; field_simp; ring
      rw [this, hxdef, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hV0.le,
        ← Real.rpow_mul ht.le]
      rw [show L * (1 / L) = 1 by field_simp, Real.rpow_one]
      congr 2
      field_simp
    have : (M * x t + x t * (p / (p + L))) / (L * x t ^ (M / L)) =
        (M + p / (p + L)) / L * (x t / x t ^ (M / L)) := by
      have : x t ^ (M / L) ≠ 0 := (Real.rpow_pos_of_pos hxt _).ne'
      field_simp
    rw [this, hpow, hcform]
    ring
  -- the integrand
  have hint : ∀ t ∈ Set.uIcc (0 : ℝ) 1, cfun k n (x t) (hardyAvg x t) =
      N / (N + 1) * (c * V) ^ (N + 1) * t ^ ((N + 1) / p) := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    rcases ht.1.lt_or_eq with htpos | htzero
    · unfold cfun
      rw [hbid t htpos, ← hN, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul htpos.le]
      rw [show 1 / p * (N + 1) = (N + 1) / p by ring]
      ring
    · subst htzero
      have hx0 : x 0 = 0 := by
        rw [hxdef, Real.zero_rpow (by positivity), mul_zero]
      unfold cfun bidX
      rw [hx0, if_pos rfl, ← hN, Real.zero_rpow (by positivity), Real.zero_rpow (by positivity)]
      ring
  unfold Cfun
  rw [intervalIntegral.integral_congr hint, intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by linarith [show (0:ℝ) < (N + 1) / p by positivity])), Real.one_rpow, Real.zero_rpow (by positivity)]
  field_simp <;> ring
