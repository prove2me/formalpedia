-- Prove2me | solution 1 for Mandelbrot.multibrot_escape_criterion
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T16:08:55.811682+00:00
-- url     : https://prove2.me/submissions/c9736446-f809-4c9f-a332-0ea467ac008e

import Mathlib
import Definitions.Def_mandelbrot_sets

open Topology Set Function Filter Bornology Metric MeasureTheory

namespace Mandelbrot

noncomputable section

private abbrev orbitN (n : ℕ) (c : ℂ) (k : ℕ) : ℂ :=
  (fun z ↦ z ^ n + c)^[k] 0

private abbrev escapeRadius (n : ℕ) : ℝ :=
  (2 : ℝ) ^ (((n : ℝ) - 1)⁻¹)

private lemma orbitN_one (n : ℕ) (c : ℂ) (hn0 : n ≠ 0) : orbitN n c 1 = c := by
  simp [orbitN, hn0]

private lemma orbitN_succ (n : ℕ) (c : ℂ) (k : ℕ) :
    orbitN n c (k + 1) = orbitN n c k ^ n + c := by
  simp [orbitN, Function.iterate_succ_apply']

private lemma escapeRadius_pow_sub_one {n : ℕ} (hn : 2 ≤ n) :
    escapeRadius n ^ (n - 1) = 2 := by
  have hn1 : n - 1 ≠ 0 := by omega
  have hcast : (n : ℝ) - 1 = ((n - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  rw [escapeRadius, hcast]
  exact Real.rpow_inv_natCast_pow (by norm_num) hn1

private lemma one_lt_escapeRadius {n : ℕ} (hn : 2 ≤ n) :
    1 < escapeRadius n := by
  apply Real.one_lt_rpow (by norm_num)
  apply inv_pos.mpr
  exact sub_pos.mpr (by exact_mod_cast (show 1 < n by omega))

/-- Above the escape radius, the orbit dominates a geometric progression. -/
private lemma orbitN_geometric_growth (n : ℕ) (c : ℂ) (j : ℕ) (hn : 2 ≤ n)
    (hjR : escapeRadius n < ‖orbitN n c j‖)
    (hjc : ‖c‖ ≤ ‖orbitN n c j‖) :
    ∀ m : ℕ,
      ‖orbitN n c j‖ * (‖orbitN n c j‖ ^ (n - 1) - 1) ^ m ≤
        ‖orbitN n c (j + m)‖ := by
  have hn1 : n - 1 ≠ 0 := by omega
  have hpowj : 2 < ‖orbitN n c j‖ ^ (n - 1) := by
    rw [← escapeRadius_pow_sub_one hn]
    exact pow_lt_pow_left₀ hjR
      (le_trans (by norm_num) (le_of_lt (one_lt_escapeRadius hn))) hn1
  have hbase : 1 < ‖orbitN n c j‖ ^ (n - 1) - 1 := by linarith
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      have hmono : ‖orbitN n c j‖ ≤ ‖orbitN n c (j + m)‖ := by
        calc
          ‖orbitN n c j‖ =
              ‖orbitN n c j‖ * (‖orbitN n c j‖ ^ (n - 1) - 1) ^ 0 := by ring
          _ ≤ ‖orbitN n c j‖ *
              (‖orbitN n c j‖ ^ (n - 1) - 1) ^ m := by
                exact mul_le_mul_of_nonneg_left (one_le_pow₀ hbase.le) (norm_nonneg _)
          _ ≤ ‖orbitN n c (j + m)‖ := ih
      have hc : ‖c‖ ≤ ‖orbitN n c (j + m)‖ := hjc.trans hmono
      have hpowers :
          ‖orbitN n c j‖ ^ (n - 1) ≤ ‖orbitN n c (j + m)‖ ^ (n - 1) :=
        pow_le_pow_left₀ (norm_nonneg _) hmono _
      have hnext :
          ‖orbitN n c (j + m)‖ * (‖orbitN n c j‖ ^ (n - 1) - 1) ≤
            ‖orbitN n c (j + m + 1)‖ := by
        rw [orbitN_succ]
        calc
          ‖orbitN n c (j + m)‖ * (‖orbitN n c j‖ ^ (n - 1) - 1)
              ≤ ‖orbitN n c (j + m)‖ *
                  (‖orbitN n c (j + m)‖ ^ (n - 1) - 1) := by
                    exact mul_le_mul_of_nonneg_left (sub_le_sub_right hpowers 1) (norm_nonneg _)
          _ = ‖orbitN n c (j + m)‖ ^ n - ‖orbitN n c (j + m)‖ := by
                rw [mul_sub, mul_one, ← pow_succ']
                congr 2
                omega
          _ ≤ ‖orbitN n c (j + m)‖ ^ n - ‖c‖ := by linarith
          _ ≤ ‖orbitN n c (j + m) ^ n + c‖ := by
                have htri := norm_sub_le (orbitN n c (j + m) ^ n + c) c
                rw [add_sub_cancel_right, norm_pow] at htri
                linarith
      rw [pow_succ]
      calc
        ‖orbitN n c j‖ *
              ((‖orbitN n c j‖ ^ (n - 1) - 1) ^ m *
                (‖orbitN n c j‖ ^ (n - 1) - 1)) =
            (‖orbitN n c j‖ * (‖orbitN n c j‖ ^ (n - 1) - 1) ^ m) *
              (‖orbitN n c j‖ ^ (n - 1) - 1) := by ring
        _ ≤ ‖orbitN n c (j + m)‖ *
              (‖orbitN n c j‖ ^ (n - 1) - 1) := by gcongr
        _ ≤ ‖orbitN n c (j + m + 1)‖ := hnext

private lemma orbitN_tendsto_cobounded_of_escape (n : ℕ) (c : ℂ) (hn : 2 ≤ n) {k : ℕ}
    (hk : escapeRadius n < ‖orbitN n c k‖) :
    Tendsto (orbitN n c) atTop (cobounded ℂ) := by
  let j := if escapeRadius n < ‖c‖ then 1 else k
  have hn0 : n ≠ 0 := by omega
  have hjR : escapeRadius n < ‖orbitN n c j‖ := by
    dsimp [j]
    split_ifs with hc
    · simpa [orbitN_one n c hn0] using hc
    · exact hk
  have hjc : ‖c‖ ≤ ‖orbitN n c j‖ := by
    dsimp [j]
    split_ifs with hc
    · simp [orbitN_one n c hn0]
    · exact (le_of_not_gt hc).trans (le_of_lt hk)
  have hbase : 1 < ‖orbitN n c j‖ ^ (n - 1) - 1 := by
    have hn1 : n - 1 ≠ 0 := by omega
    have hpowj : 2 < ‖orbitN n c j‖ ^ (n - 1) := by
      rw [← escapeRadius_pow_sub_one hn]
      exact pow_lt_pow_left₀ hjR
        (le_trans (by norm_num) (le_of_lt (one_lt_escapeRadius hn))) hn1
    linarith
  have hgeom : Tendsto
      (fun m : ℕ ↦ ‖orbitN n c j‖ *
        (‖orbitN n c j‖ ^ (n - 1) - 1) ^ m) atTop atTop := by
    simpa [mul_comm] using
      (tendsto_pow_atTop_atTop_of_one_lt hbase).atTop_mul_const
          (lt_trans (lt_trans (by norm_num) (one_lt_escapeRadius hn)) hjR)
  have hshift : Tendsto (fun m : ℕ ↦ ‖orbitN n c (j + m)‖) atTop atTop :=
    tendsto_atTop_mono' atTop
      (Eventually.of_forall (orbitN_geometric_growth n c j hn hjR hjc)) hgeom
  have hnorm : Tendsto (fun m : ℕ ↦ ‖orbitN n c m‖) atTop atTop := by
    rw [← tendsto_add_atTop_iff_nat j]
    simpa [Nat.add_comm] using hshift
  exact tendsto_norm_atTop_iff_cobounded.mp hnorm

theorem multibrotEscapeProof {n : ℕ} (hn : 2 ≤ n) :
    multibrotSet n =
      {c : ℂ | ∀ k : ℕ, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ escapeRadius n} := by
  ext c
  simp only [multibrotSet, Set.mem_ofPred_eq]
  constructor
  · intro hnT k
    by_contra hk
    exact hnT (orbitN_tendsto_cobounded_of_escape n c hn (lt_of_not_ge hk))
  · intro hbounded htend
    have hnorm : Tendsto (fun k : ℕ ↦ ‖orbitN n c k‖) atTop atTop :=
      tendsto_norm_atTop_iff_cobounded.mpr htend
    obtain ⟨k, hk⟩ := (hnorm.eventually_gt_atTop (escapeRadius n)).exists
    exact (not_lt_of_ge (hbounded k)) hk

end

end Mandelbrot

theorem solution {n : ℕ} (hn : 2 ≤ n) :
    Mandelbrot.multibrotSet n =
      {c : ℂ | ∀ k : ℕ,
        ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ (2 : ℝ) ^ (((n : ℝ) - 1)⁻¹)} :=
  Mandelbrot.multibrotEscapeProof hn
