-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.clbi_affine_unit_propagation_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T18:19:05.021978+00:00
-- url     : https://prove2.me/submissions/1de6f050-5e74-48c4-a3eb-e842145d4d8b

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open NestedSeatAlloc.IntPolicy

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f : ℕ → ℝ) (hM : IsSeatModel P X f)
    (hint : ∀ k ω, ∃ n : ℕ, X k ω = n) (p : ℕ → ℕ) :
    ∀ m : ℕ, ∃ a b : ℝ,
      ∀ s ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1),
        expRevenue P X f (fun j => (p j : ℝ)) 1 s = a + b * s := by
  letI : IsProbabilityMeasure P := hM.isProb
  have hXnonneg : ∀ ω, 0 ≤ X 1 ω := by
    intro ω
    rcases hint 1 ω with ⟨n, hn⟩
    rw [hn]
    exact_mod_cast (Nat.zero_le n)
  intro m
  let A : Set Ω := {ω | X 1 ω ≤ (m : ℝ)}
  let B : Set Ω := {ω | (m : ℝ) < X 1 ω}
  let c : Ω → ℝ := A.indicator (fun ω => f 1 * X 1 ω)
  let d : Ω → ℝ := B.indicator (fun _ => f 1)
  have hA : MeasurableSet A := by
    dsimp [A]
    exact measurableSet_le (hM.meas 1) measurable_const
  have hB : MeasurableSet B := by
    dsimp [B]
    exact measurableSet_lt measurable_const (hM.meas 1)
  have hcMeas : Measurable c := by
    dsimp [c]
    exact (measurable_const.mul (hM.meas 1)).indicator hA
  have hdMeas : Measurable d := by
    dsimp [d]
    exact measurable_const.indicator hB
  have hcMajorant : Integrable
      (fun _ : Ω => |f 1| * ((m : ℝ) + 1)) P := integrable_const _
  have hcInt : Integrable c P := by
    refine hcMajorant.mono' hcMeas.aestronglyMeasurable ?_
    filter_upwards [] with ω
    change ‖A.indicator (fun ω => f 1 * X 1 ω) ω‖ ≤
      |f 1| * ((m : ℝ) + 1)
    rw [Set.indicator_apply]
    by_cases hω : ω ∈ A
    · simp only [hω, if_pos]
      change X 1 ω ≤ (m : ℝ) at hω
      have hx := hXnonneg ω
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hx]
      calc
        |f 1| * X 1 ω ≤ |f 1| * (m : ℝ) :=
          mul_le_mul_of_nonneg_left hω (abs_nonneg _)
        _ ≤ |f 1| * ((m : ℝ) + 1) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          norm_num
    · simpa [hω, Real.norm_eq_abs] using
        (mul_nonneg (abs_nonneg (f 1))
          (add_nonneg (Nat.cast_nonneg m) (by norm_num : (0 : ℝ) ≤ 1)))
  have hdMajorant : Integrable (fun _ : Ω => |f 1|) P := integrable_const _
  have hdInt : Integrable d P := by
    refine hdMajorant.mono' hdMeas.aestronglyMeasurable ?_
    filter_upwards [] with ω
    change ‖B.indicator (fun _ => f 1) ω‖ ≤ |f 1|
    rw [Set.indicator_apply]
    by_cases hω : ω ∈ B
    · simp [hω, Real.norm_eq_abs]
    · simp [hω]
  refine ⟨∫ ω, c ω ∂P, ∫ ω, d ω ∂P, ?_⟩
  intro s hs
  have hpoint : ∀ ω, f 1 * min s (X 1 ω) = c ω + d ω * s := by
    intro ω
    rcases hint 1 ω with ⟨n, hn⟩
    by_cases hmn : m < n
    · have hnext : m + 1 ≤ n := by omega
      have hnextR : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hnext
      have hsX : s ≤ X 1 ω := by
        rw [hn]
        exact le_trans hs.2 hnextR
      have hnotA : ω ∉ A := by
        simp only [A, Set.mem_setOf_eq]
        rw [hn]
        exact_mod_cast (Nat.not_le_of_gt hmn)
      have hBmem : ω ∈ B := by
        simp only [B, Set.mem_setOf_eq]
        rw [hn]
        exact_mod_cast hmn
      simp [c, d, hnotA, hBmem, min_eq_left hsX]
    · have hnm : n ≤ m := Nat.le_of_not_gt hmn
      have hnmR : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
      have hnS : (n : ℝ) ≤ s := le_trans hnmR hs.1
      have hAmem : ω ∈ A := by
        simp only [A, Set.mem_setOf_eq]
        rw [hn]
        exact_mod_cast hnm
      have hnotB : ω ∉ B := by
        simp only [B, Set.mem_setOf_eq]
        rw [hn]
        exact not_lt_of_ge (by exact_mod_cast hnm)
      have hXs : X 1 ω ≤ s := by rw [hn]; exact hnS
      simp [c, d, hAmem, hnotB, min_eq_right hXs]
  calc
    expRevenue P X f (fun j => (p j : ℝ)) 1 s =
        ∫ ω, c ω + d ω * s ∂P := by
          rw [expRevenue]
          apply integral_congr_ae
          filter_upwards [] with ω
          change (if s < X 1 ω then f 1 * s else f 1 * X 1 ω) =
            c ω + d ω * s
          calc
            (if s < X 1 ω then f 1 * s else f 1 * X 1 ω) =
                f 1 * min s (X 1 ω) := by
                  by_cases hsX : s < X 1 ω
                  · simp [hsX, min_eq_left (le_of_lt hsX)]
                  · have hXs : X 1 ω ≤ s := le_of_not_gt hsX
                    simp [hsX, min_eq_right hXs]
            _ = c ω + d ω * s := hpoint ω
    _ = (∫ ω, c ω ∂P) + (∫ ω, d ω ∂P) * s := by
          rw [integral_add hcInt (hdInt.mul_const s), integral_mul_const]
