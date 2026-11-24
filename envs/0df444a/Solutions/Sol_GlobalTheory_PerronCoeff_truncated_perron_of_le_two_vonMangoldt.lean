-- Prove2me | solution 1 for GlobalTheory.PerronCoeff.truncated_perron_of_le_two_vonMangoldt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:47:04.263075+00:00
-- url     : https://prove2.me/submissions/2e74ae87-37b7-4c2c-9adc-b25322e228e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TruncatedPerronPsi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TruncatedPerronOfLeTwoVonMangoldt
import Theorems.Thm_GlobalTheory_PerronKernel_hbound
import Theorems.Thm_GlobalTheory_PerronPsi_far_term
import Theorems.Thm_GlobalTheory_PerronPsi_half_le_log
import Theorems.Thm_GlobalTheory_PerronPsi_interchange
import Theorems.Thm_GlobalTheory_PerronPsi_kernel_bound
import Theorems.Thm_GlobalTheory_PerronPsi_near_term
import Theorems.Thm_GlobalTheory_PerronPsi_sum_w
import Theorems.Thm_GlobalTheory_PerronPsi_w_nonneg
import Theorems.Thm_GlobalTheory_PerronPsi_zeta_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.PerronCoeff
open GlobalTheory.PerronPsi
namespace GlobalTheory.PerronCoeff
theorem _root_.solution : ∃ C : ℝ, 0 < C ∧ ∀ (c : ℕ → ℂ) (u T : ℝ), (∀ n, ‖c n‖ ≤ 2 * Λ n) → 2 ≤ T → T ≤ u → ‖(∑ n ∈ Finset.Icc 1 ⌊u⌋₊, c n) - (1 / (2 * Real.pi) : ℂ) * ∫ t in (-T)..T, LSeries c (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I) * (u : ℂ) ^ (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I) / (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I)‖ ≤ C * (u * Real.log u ^ 2 / T + Real.log u) := by
  obtain ⟨C, hC, hK⟩ := kernel_bound
  refine ⟨480 * C, by positivity, ?_⟩
  intro c u T hc hT hTu
  have hu : 2 ≤ u := hT.trans hTu
  have hu0 : 0 < u := by linarith
  have hT0 : 0 < T := by linarith
  have hL : 1 / 2 ≤ Real.log u := half_le_log hu
  have hL0 : 0 < Real.log u := by linarith
  have hσ1 : 1 < 1 + 1 / Real.log u := by
    have : 0 < 1 / Real.log u := by positivity
    linarith
  have hσ0 : 0 < 1 + 1 / Real.log u := by linarith
  have hc0 : c 0 = 0 := by simpa using hc 0
  have hs : LSeriesSummable c ((1 + 1 / Real.log u : ℝ) : ℂ) := by
    have hΛ : LSeriesSummable (fun n => (Λ n : ℂ)) ((1 + 1 / Real.log u : ℝ) : ℂ) :=
      ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ1)
    refine Summable.of_norm_bounded (hΛ.norm.mul_left 2) (fun n => ?_)
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    split_ifs with hn
    · simp
    · have hpow : 0 < (n : ℝ) ^ (((1 + 1 / Real.log u : ℝ) : ℂ)).re := by
        have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
        positivity
      rw [Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
        mul_div_assoc']
      exact div_le_div_of_nonneg_right (hc n) hpow.le
  have hI := interchange c hc0 T hσ0 hu0 hs
  have hS : HasSum (fun n : ℕ => c n * (if 1 ≤ u / (n : ℝ) then (1 : ℂ) else 0))
      (∑ n ∈ Finset.Icc 1 ⌊u⌋₊, c n) := by
    have e : ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, c n
        = ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, c n * (if 1 ≤ u / (n : ℝ) then (1 : ℂ) else 0) := by
      refine Finset.sum_congr rfl (fun n hn => ?_)
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast h1
      have : 1 ≤ u / n := by
        rw [le_div_iff₀ hn0, one_mul]
        exact (Nat.le_floor_iff hu0.le).mp h2
      simp [this]
    rw [e]
    apply hasSum_sum_of_ne_finset_zero
    intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp [hc0]
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast hpos
      have : ¬ (1 ≤ u / n) := by
        intro h
        apply hn
        rw [le_div_iff₀ hn0, one_mul] at h
        exact Finset.mem_Icc.mpr ⟨hpos, Nat.le_floor h⟩
      simp [this]
  have hD := hS.sub (hI.mul_left (1 / (2 * Real.pi) : ℂ))
  have hfac : ∀ x y z v : ℂ, x * y - z * (x * v) = x * (y - z * v) := fun _ _ _ _ => by ring
  have hp : 1 < 1 + 1 / (2 * Real.log u) := by
    have : 0 < 1 / (2 * Real.log u) := by positivity
    linarith
  have hsumm : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (1 + 1 / (2 * Real.log u))) :=
    Real.summable_one_div_nat_rpow.mpr hp
  have hB : 0 ≤ 2 * u / T := by positivity
  have hnear : HasSum (fun n : ℕ =>
        if n ∈ Finset.range (⌊u⌋₊ + 1 + (⌊u⌋₊ + 1)) then w ⌊u⌋₊ (2 * u / T) n else 0)
      (∑ n ∈ Finset.range (⌊u⌋₊ + 1 + (⌊u⌋₊ + 1)), w ⌊u⌋₊ (2 * u / T) n) := by
    have e : ∑ n ∈ Finset.range (⌊u⌋₊ + 1 + (⌊u⌋₊ + 1)), w ⌊u⌋₊ (2 * u / T) n
        = ∑ n ∈ Finset.range (⌊u⌋₊ + 1 + (⌊u⌋₊ + 1)),
          (if n ∈ Finset.range (⌊u⌋₊ + 1 + (⌊u⌋₊ + 1)) then w ⌊u⌋₊ (2 * u / T) n else 0) :=
      Finset.sum_congr rfl (fun n hn => by simp [hn])
    rw [e]
    apply hasSum_sum_of_ne_finset_zero
    intro n hn
    simp [hn]
  have hg := (hsumm.hasSum.mul_left (2 * C * (12 * u * Real.log u / T))).add
    (hnear.mul_left (2 * C * (16 * Real.log u)))
  have hA0 : 0 ≤ 2 * C * (12 * u * Real.log u / T) := by positivity
  have hBc0 : 0 ≤ 2 * C * (16 * Real.log u) := by positivity
  have hbound := hD.norm_le_of_bounded hg (fun n => by
    rw [hfac]
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp only [hc0, zero_mul, norm_zero]
      refine add_nonneg (mul_nonneg hA0 (by positivity)) (mul_nonneg hBc0 ?_)
      split_ifs
      · exact w_nonneg _ hB _
      · exact le_rfl
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hpos
    have hy : 0 < u / n := div_pos hu0 hn0
    obtain ⟨hK1, hK2⟩ := hK (u / n) (1 + 1 / Real.log u) T hy hσ0 (by linarith)
    have hE0 := norm_nonneg ((1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T,
        ((u / n : ℝ) : ℂ) ^ (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I)
          / (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I)) - (if 1 ≤ u / n then 1 else 0))
    rw [norm_mul, norm_sub_rev]
    have hcn : ‖c n‖ ≤ 2 * Real.log n :=
      (hc n).trans (by linarith [ArithmeticFunction.vonMangoldt_le_log (n := n)])
    have hmain := mul_le_mul_of_nonneg_right hcn hE0
    have hfar0 : 0 ≤ 2 * C * (12 * u * Real.log u / T)
        * (1 / (n : ℝ) ^ (1 + 1 / (2 * Real.log u))) := mul_nonneg hA0 (by positivity)
    by_cases hfar : (n : ℝ) ≤ u / 2 ∨ 2 * u ≤ n
    · have h := far_term hu hT0 hpos hC.le hE0 hK2 hfar
      have hnr : 0 ≤ 2 * C * (16 * Real.log u)
          * (if n ∈ Finset.range (⌊u⌋₊ + 1 + (⌊u⌋₊ + 1)) then w ⌊u⌋₊ (2 * u / T) n else 0) := by
        refine mul_nonneg hBc0 ?_
        split_ifs
        · exact w_nonneg _ hB _
        · exact le_rfl
      nlinarith
    · push Not at hfar
      have h := near_term hu hT0 hC.le hE0 hK1 hK2 hfar.1 hfar.2
      have hmem : n ∈ Finset.range (⌊u⌋₊ + 1 + (⌊u⌋₊ + 1)) := by
        rw [Finset.mem_range]
        have h1 : u < (⌊u⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one u
        have h2 : (n : ℝ) < ((⌊u⌋₊ + 1 + (⌊u⌋₊ + 1) : ℕ) : ℝ) := by
          push_cast
          linarith [hfar.2]
        exact_mod_cast h2
      rw [if_pos hmem]
      nlinarith)
  refine hbound.trans ?_
  have hZ : ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + 1 / (2 * Real.log u)) ≤ 1 + 2 * Real.log u := by
    have h := zeta_bound hp
    have e : 1 / (1 + 1 / (2 * Real.log u) - 1) = 2 * Real.log u := by
      rw [add_sub_cancel_left, one_div_one_div]
    rwa [e] at h
  have hN : Real.log ⌊u⌋₊ ≤ Real.log u := by
    have hpos : (0 : ℝ) < ⌊u⌋₊ := by
      have : 1 ≤ ⌊u⌋₊ := Nat.le_floor (by norm_num; linarith)
      exact_mod_cast this
    exact Real.log_le_log hpos (Nat.floor_le hu0.le)
  have hW : ∑ n ∈ Finset.range (⌊u⌋₊ + 1 + (⌊u⌋₊ + 1)), w ⌊u⌋₊ (2 * u / T) n
      ≤ 2 + 2 * u / T * (2 * (1 + Real.log u)) := by
    have h := sum_w ⌊u⌋₊ hB
    have : 2 * u / T * (2 * (1 + Real.log ⌊u⌋₊)) ≤ 2 * u / T * (2 * (1 + Real.log u)) := by
      gcongr
    linarith
  have hX : 0 ≤ u / T := by positivity
  have hint : 0 ≤ (u / T) * Real.log u * (2 * Real.log u - 1) :=
    mul_nonneg (mul_nonneg hX hL0.le) (by linarith)
  have key : 2 * (12 * (u / T) * Real.log u) * (1 + 2 * Real.log u)
      + 2 * (16 * Real.log u) * (2 + 2 * (u / T) * (2 * (1 + Real.log u)))
      ≤ 480 * ((u / T) * Real.log u ^ 2 + Real.log u) := by
    nlinarith
  calc 2 * C * (12 * u * Real.log u / T) * ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + 1 / (2 * Real.log u))
        + 2 * C * (16 * Real.log u)
          * ∑ n ∈ Finset.range (⌊u⌋₊ + 1 + (⌊u⌋₊ + 1)), w ⌊u⌋₊ (2 * u / T) n
      ≤ 2 * C * (12 * u * Real.log u / T) * (1 + 2 * Real.log u)
        + 2 * C * (16 * Real.log u) * (2 + 2 * u / T * (2 * (1 + Real.log u))) := by
        gcongr
    _ = C * (2 * (12 * (u / T) * Real.log u) * (1 + 2 * Real.log u)
        + 2 * (16 * Real.log u) * (2 + 2 * (u / T) * (2 * (1 + Real.log u)))) := by ring
    _ ≤ C * (480 * ((u / T) * Real.log u ^ 2 + Real.log u)) :=
        mul_le_mul_of_nonneg_left key hC.le
    _ = 480 * C * (u * Real.log u ^ 2 / T + Real.log u) := by ring
end GlobalTheory.PerronCoeff
