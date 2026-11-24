-- Prove2me | solution 1 for GlobalTheory.PerronPsi.truncated_perron_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:46:57.750856+00:00
-- url     : https://prove2.me/submissions/59e60783-1ce6-40e5-a567-f85918e27fd9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TruncatedPerronKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TruncatedPerronPsi
import Theorems.Thm_GlobalTheory_PerronPsi_kernel_bound
import Theorems.Thm_GlobalTheory_PerronPsi_interchange
import Theorems.Thm_GlobalTheory_PerronPsi_zeta_bound
import Theorems.Thm_GlobalTheory_PerronPsi_w_nonneg
import Theorems.Thm_GlobalTheory_PerronPsi_sum_w
import Theorems.Thm_GlobalTheory_PerronPsi_half_le_log
import Theorems.Thm_GlobalTheory_PerronPsi_far_term
import Theorems.Thm_GlobalTheory_PerronPsi_near_term

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.PerronPsi
namespace GlobalTheory.PerronPsi
theorem _root_.solution : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (u T : ℝ), 2 ≤ T → T ≤ 2 * u → 2 ≤ u → ‖(∑ n ∈ Finset.Icc 1 ⌊u⌋₊, (Λ n : ℂ) * χ (n : ZMod q)) - (1 / (2 * Real.pi) : ℂ) * ∫ t in (-T)..T, -(deriv (LFunction χ) ((1 + 1 / Real.log u : ℝ) + t * I) / LFunction χ ((1 + 1 / Real.log u : ℝ) + t * I)) * (u : ℂ) ^ (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I) / ((1 + 1 / Real.log u : ℝ) + t * I)‖ ≤ C * (u * Real.log u ^ 2 / T + Real.log u) := by
  obtain ⟨C0, hC0, hK⟩ := kernel_bound
  refine ⟨240 * C0, by positivity, ?_⟩
  intro q _ χ u T hT2 hTu hu
  have hu0 : 0 < u := by linarith
  have hT0 : 0 < T := by linarith
  have hL := half_le_log hu
  set L := Real.log u with hLdef
  have hL0 : 0 < L := by linarith
  set σ : ℝ := 1 + 1 / L with hσ
  have hσ1 : 1 < σ := by
    have := one_div_pos.2 hL0
    linarith
  set N := ⌊u⌋₊ with hN
  set B := 2 * u / T with hB
  have hB0 : 0 ≤ B := div_nonneg (by linarith) hT0.le
  set a : ℕ → ℂ := fun n => (Λ n : ℂ) * χ (n : ZMod q) with ha
  have ha0 : a 0 = 0 := by simp [ha]
  have hre : ∀ t : ℝ, 1 < ((σ : ℂ) + t * I).re := fun t => by simpa using hσ1
  have hsum : LSeriesSummable a σ := by
    have h1 := LSeriesSummable_twist_vonMangoldt χ (s := (σ : ℂ)) (by simpa using hσ1)
    convert h1 using 1
    funext n
    simp only [ha, Pi.mul_apply]
    ring
  have hLS : ∀ t : ℝ, -(deriv (LFunction χ) ((σ : ℂ) + t * I) / LFunction χ ((σ : ℂ) + t * I))
      = LSeries a ((σ : ℂ) + t * I) := by
    intro t
    rw [LFunction_eq_LSeries χ (hre t), deriv_LFunction_eq_deriv_LSeries χ (hre t), ← neg_div,
      ← LSeries_twist_vonMangoldt_eq χ (hre t)]
    congr 1
    funext n
    simp only [ha, Pi.mul_apply]
    ring
  have hJ : ∫ t in (-T)..T, -(deriv (LFunction χ) ((σ : ℂ) + t * I) / LFunction χ ((σ : ℂ) + t * I))
        * (u : ℂ) ^ ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I)
      = ∫ t in (-T)..T, LSeries a ((σ : ℂ) + t * I) * (u : ℂ) ^ ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I) := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only
    rw [hLS t]
  have hI := interchange a ha0 T (one_pos.trans hσ1) hu0 hsum
  have hfin : HasSum (fun n => a n * (if 1 ≤ u / n then (1 : ℂ) else 0)) (∑ n ∈ Finset.Icc 1 N, a n) := by
    have h : HasSum (fun n => a n * (if 1 ≤ u / n then (1 : ℂ) else 0))
        (∑ n ∈ Finset.Icc 1 N, a n * (if 1 ≤ u / n then (1 : ℂ) else 0)) :=
      hasSum_sum_of_ne_finset_zero (by
        intro n hn
        by_cases h0 : n = 0
        · simp [h0, ha0]
        · have hnN : N < n := by
            rw [Finset.mem_Icc] at hn
            omega
          have hlt : u < n := (Nat.floor_lt hu0.le).1 hnN
          have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero h0
          have hnot : ¬ (1 ≤ u / n) := by
            rw [not_le, div_lt_one hnpos]
            exact hlt
          simp [hnot])
    convert h using 1
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hle : (n : ℝ) ≤ u := (Nat.le_floor_iff hu0.le).1 hn.2
    have h1 : 1 ≤ u / n := by rw [le_div_iff₀ hnpos]; linarith
    simp [h1]
  have hcomb := hfin.sub (hI.mul_left (1 / (2 * Real.pi) : ℂ))
  have hτ1 : 1 < 1 + 1 / (2 * L) := by
    have := one_div_pos.2 (show 0 < 2 * L by linarith)
    linarith
  have hs1 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (1 + 1 / (2 * L))) :=
    Real.summable_one_div_nat_rpow.2 hτ1
  have hA : 0 ≤ 12 * u * L / T :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hu0.le) hL0.le) hT0.le
  have hW0 : ∀ n, 0 ≤ (if n ∈ Finset.range (N + 1 + (N + 1)) then w N B n else 0) := by
    intro n
    split_ifs
    · exact w_nonneg N hB0 n
    · exact le_rfl
  have hg : HasSum (fun n : ℕ => C0 * (12 * u * L / T * (1 / (n : ℝ) ^ (1 + 1 / (2 * L))))
        + C0 * (16 * L * (if n ∈ Finset.range (N + 1 + (N + 1)) then w N B n else 0)))
      (C0 * (12 * u * L / T * ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + 1 / (2 * L)))
        + C0 * (16 * L * ∑ n ∈ Finset.range (N + 1 + (N + 1)),
          (if n ∈ Finset.range (N + 1 + (N + 1)) then w N B n else 0))) := by
    refine HasSum.add ((hs1.hasSum.mul_left _).mul_left _) ((HasSum.mul_left _ ?_).mul_left _)
    exact hasSum_sum_of_ne_finset_zero (fun n hn => if_neg hn)
  have hpt : ∀ n : ℕ, ‖a n * (if 1 ≤ u / n then (1 : ℂ) else 0)
      - (1 / (2 * Real.pi) : ℂ) * (a n * ∫ t in (-T)..T,
        ((u / n : ℝ) : ℂ) ^ ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I))‖
      ≤ C0 * (12 * u * L / T * (1 / (n : ℝ) ^ (1 + 1 / (2 * L))))
        + C0 * (16 * L * (if n ∈ Finset.range (N + 1 + (N + 1)) then w N B n else 0)) := by
    intro n
    have hg1 : 0 ≤ C0 * (12 * u * L / T * (1 / (n : ℝ) ^ (1 + 1 / (2 * L)))) :=
      mul_nonneg hC0.le (mul_nonneg hA (by positivity))
    have hg2 : 0 ≤ C0 * (16 * L * (if n ∈ Finset.range (N + 1 + (N + 1)) then w N B n else 0)) :=
      mul_nonneg hC0.le (mul_nonneg (by linarith) (hW0 n))
    by_cases h0 : n = 0
    · subst h0
      rw [ha0]
      simp only [zero_mul, mul_zero, sub_zero, norm_zero]
      linarith
    have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero h0
    have e : a n * (if 1 ≤ u / n then (1 : ℂ) else 0)
        - (1 / (2 * Real.pi) : ℂ) * (a n * ∫ t in (-T)..T,
          ((u / n : ℝ) : ℂ) ^ ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I))
        = -(a n * ((1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T,
          ((u / n : ℝ) : ℂ) ^ ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I))
          - (if 1 ≤ u / n then (1 : ℂ) else 0))) := by ring
    rw [e, norm_neg, norm_mul]
    have han : ‖a n‖ ≤ Real.log n := by
      show ‖(Λ n : ℂ) * χ (n : ZMod q)‖ ≤ Real.log n
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
      calc Λ n * ‖χ (n : ZMod q)‖ ≤ Λ n * 1 :=
            mul_le_mul_of_nonneg_left (χ.norm_le_one _) vonMangoldt_nonneg
        _ ≤ Real.log n := by rw [mul_one]; exact vonMangoldt_le_log
    obtain ⟨hk1, hk2⟩ := hK (u / n) σ T (div_pos hu0 hn0) (one_pos.trans hσ1) (by linarith)
    have hstep := mul_le_mul_of_nonneg_right han (norm_nonneg
      ((1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T,
          ((u / n : ℝ) : ℂ) ^ ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I))
          - (if 1 ≤ u / n then (1 : ℂ) else 0)))
    by_cases hfar : (n : ℝ) ≤ u / 2 ∨ 2 * u ≤ n
    · have hft := far_term hu hT0 (Nat.pos_of_ne_zero h0) hC0.le (norm_nonneg _) hk2 hfar
      linarith
    · push Not at hfar
      obtain ⟨h1, h2⟩ := hfar
      have hnt := near_term hu hT0 hC0.le (norm_nonneg _) hk1 hk2 h1 h2
      have hmem : n ∈ Finset.range (N + 1 + (N + 1)) := by
        have huN : u < (N : ℝ) + 1 := Nat.lt_floor_add_one u
        have h3 : (n : ℝ) < ((N + 1 + (N + 1) : ℕ) : ℝ) := by
          push_cast
          linarith
        rw [Finset.mem_range]
        exact_mod_cast h3
      rw [if_pos hmem]
      linarith
  have key := hcomb.norm_le_of_bounded hg hpt
  have hZ : ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + 1 / (2 * L)) ≤ 1 + 2 * L := by
    have h1 := zeta_bound hτ1
    rwa [add_sub_cancel_left, one_div_one_div] at h1
  have hWeq : ∑ n ∈ Finset.range (N + 1 + (N + 1)),
      (if n ∈ Finset.range (N + 1 + (N + 1)) then w N B n else 0)
      = ∑ n ∈ Finset.range (N + 1 + (N + 1)), w N B n :=
    Finset.sum_congr rfl (fun n hn => if_pos hn)
  have hlogN : Real.log N ≤ L := by
    have h2 : (2 : ℕ) ≤ N := Nat.le_floor (by exact_mod_cast hu)
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    exact Real.log_le_log hNpos (Nat.floor_le hu0.le)
  have hW : ∑ n ∈ Finset.range (N + 1 + (N + 1)), w N B n ≤ 2 + B * (2 * (1 + L)) := by
    have h1 := sum_w N hB0
    have h2 : B * (2 * (1 + Real.log N)) ≤ B * (2 * (1 + L)) :=
      mul_le_mul_of_nonneg_left (by linarith) hB0
    linarith
  rw [hJ]
  refine key.trans ?_
  rw [hWeq]
  have hX : 0 < u / T := div_pos hu0 hT0
  have e1 : 12 * u * L / T = 12 * L * (u / T) := by ring
  have e2 : B = 2 * (u / T) := by rw [hB]; ring
  have e3 : u * L ^ 2 / T = L ^ 2 * (u / T) := by ring
  have b1 := mul_le_mul_of_nonneg_left hZ hA
  have b2 := mul_le_mul_of_nonneg_left hW (show (0 : ℝ) ≤ 16 * L by linarith)
  have b3 : 12 * u * L / T * (1 + 2 * L) + 16 * L * (2 + B * (2 * (1 + L)))
      ≤ 240 * (u * L ^ 2 / T + L) := by
    rw [e1, e2, e3]
    nlinarith [mul_nonneg (mul_nonneg hL0.le hX.le) (show (0 : ℝ) ≤ 2 * L - 1 by linarith),
      mul_nonneg (mul_nonneg hL0.le hL0.le) hX.le]
  have b4 : 12 * u * L / T * ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + 1 / (2 * L))
      + 16 * L * ∑ n ∈ Finset.range (N + 1 + (N + 1)), w N B n ≤ 240 * (u * L ^ 2 / T + L) := by
    linarith
  have b5 := mul_le_mul_of_nonneg_left b4 hC0.le
  linarith
end GlobalTheory.PerronPsi
