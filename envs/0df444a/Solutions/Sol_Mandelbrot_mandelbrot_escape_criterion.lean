-- Prove2me | solution 1 for Mandelbrot.mandelbrot_escape_criterion
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T15:59:14.047401+00:00
-- url     : https://prove2.me/submissions/10c8c91f-6d1e-460e-88a6-7a61d30e140d

import Mathlib
import Definitions.Def_mandelbrot_sets

open Topology Set Function Filter Bornology Metric MeasureTheory

namespace Mandelbrot

private abbrev orbit (c : ℂ) (k : ℕ) : ℂ :=
  (fun z ↦ z ^ 2 + c)^[k] 0

private lemma orbit_zero (c : ℂ) : orbit c 0 = 0 := by
  rfl

private lemma orbit_one (c : ℂ) : orbit c 1 = c := by
  simp [orbit]

private lemma orbit_succ (c : ℂ) (k : ℕ) :
    orbit c (k + 1) = orbit c k ^ 2 + c := by
  simp [orbit, Function.iterate_succ_apply']

/-- Once an orbit value has norm greater than two and at least the parameter norm,
all later values dominate a geometric progression. -/
private lemma orbit_geometric_growth (c : ℂ) (j : ℕ)
    (hj2 : 2 < ‖orbit c j‖) (hjc : ‖c‖ ≤ ‖orbit c j‖) :
    ∀ m : ℕ,
      ‖orbit c j‖ * (‖orbit c j‖ - 1) ^ m ≤ ‖orbit c (j + m)‖ := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      have hbase : 1 < ‖orbit c j‖ - 1 := by linarith
      have hmono : ‖orbit c j‖ ≤ ‖orbit c (j + m)‖ := by
        calc
          ‖orbit c j‖ = ‖orbit c j‖ * (‖orbit c j‖ - 1) ^ 0 := by ring
          _ ≤ ‖orbit c j‖ * (‖orbit c j‖ - 1) ^ m := by
            exact mul_le_mul_of_nonneg_left
              (one_le_pow₀ (le_of_lt hbase)) (norm_nonneg _)
          _ ≤ ‖orbit c (j + m)‖ := ih
      have hc : ‖c‖ ≤ ‖orbit c (j + m)‖ := hjc.trans hmono
      have hnext :
          ‖orbit c (j + m)‖ * (‖orbit c j‖ - 1) ≤
            ‖orbit c (j + m + 1)‖ := by
        rw [orbit_succ]
        calc
          ‖orbit c (j + m)‖ * (‖orbit c j‖ - 1)
              ≤ ‖orbit c (j + m)‖ * (‖orbit c (j + m)‖ - 1) := by
                gcongr
          _ = ‖orbit c (j + m)‖ ^ 2 - ‖orbit c (j + m)‖ := by ring
          _ ≤ ‖orbit c (j + m)‖ ^ 2 - ‖c‖ := by linarith
          _ ≤ ‖orbit c (j + m) ^ 2 + c‖ := by
            have htri := norm_sub_le (orbit c (j + m) ^ 2 + c) c
            rw [add_sub_cancel_right, norm_pow] at htri
            linarith
      rw [pow_succ]
      calc
        ‖orbit c j‖ * ((‖orbit c j‖ - 1) ^ m * (‖orbit c j‖ - 1))
            = (‖orbit c j‖ * (‖orbit c j‖ - 1) ^ m) *
                (‖orbit c j‖ - 1) := by ring
        _ ≤ ‖orbit c (j + m)‖ * (‖orbit c j‖ - 1) := by gcongr
        _ ≤ ‖orbit c (j + m + 1)‖ := hnext

private lemma orbit_tendsto_cobounded_of_escape (c : ℂ) {k : ℕ}
    (hk : 2 < ‖orbit c k‖) : Tendsto (orbit c) atTop (cobounded ℂ) := by
  let j := if 2 < ‖c‖ then 1 else k
  have hj2 : 2 < ‖orbit c j‖ := by
    dsimp [j]
    split_ifs with hc
    · simpa [orbit_one] using hc
    · exact hk
  have hjc : ‖c‖ ≤ ‖orbit c j‖ := by
    dsimp [j]
    split_ifs with hc
    · simp [orbit_one]
    · exact (le_of_not_gt hc).trans (le_of_lt hk)
  have hgeom : Tendsto
      (fun m : ℕ ↦ ‖orbit c j‖ * (‖orbit c j‖ - 1) ^ m) atTop atTop :=
    by
      simpa [mul_comm] using
        (tendsto_pow_atTop_atTop_of_one_lt
          (r := ‖orbit c j‖ - 1) (by linarith [hj2])).atTop_mul_const
          (by positivity : 0 < ‖orbit c j‖)
  have hshift : Tendsto (fun m : ℕ ↦ ‖orbit c (j + m)‖) atTop atTop :=
    tendsto_atTop_mono' atTop
      (Eventually.of_forall (orbit_geometric_growth c j hj2 hjc)) hgeom
  have hnorm : Tendsto (fun m : ℕ ↦ ‖orbit c m‖) atTop atTop := by
    rw [← tendsto_add_atTop_iff_nat j]
    simpa [Nat.add_comm] using hshift
  exact tendsto_norm_atTop_iff_cobounded.mp hnorm

theorem escapeCriterionProof :
    mandelbrotSet = {c : ℂ | ∀ k : ℕ, ‖(fun z ↦ z ^ 2 + c)^[k] 0‖ ≤ 2} := by
  ext c
  simp only [mandelbrotSet, multibrotSet, Set.mem_setOf_eq]
  constructor
  · intro hnT k
    by_contra hk
    exact hnT (orbit_tendsto_cobounded_of_escape c (lt_of_not_ge hk))
  · intro hbounded htend
    have hnorm : Tendsto (fun k : ℕ ↦ ‖orbit c k‖) atTop atTop :=
      tendsto_norm_atTop_iff_cobounded.mpr htend
    obtain ⟨k, hk⟩ := (hnorm.eventually_gt_atTop 2).exists
    exact (not_lt_of_ge (hbounded k)) hk

end Mandelbrot

theorem solution :
    Mandelbrot.mandelbrotSet =
      {c : ℂ | ∀ k : ℕ, ‖(fun z ↦ z ^ 2 + c)^[k] 0‖ ≤ 2} :=
  Mandelbrot.escapeCriterionProof
