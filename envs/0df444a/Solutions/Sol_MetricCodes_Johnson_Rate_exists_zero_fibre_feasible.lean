-- Prove2me | solution 1 for MetricCodes.Johnson.Rate.exists_zero_fibre_feasible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:31.72047+00:00
-- url     : https://prove2.me/submissions/c636363f-c1c1-4a06-8f11-c9f840b0c345

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_spectralLimit_zero_fibre_boundary

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped Topology
open MetricCodes.Johnson.Rate
open MetricCodes.Johnson.Asymptotics
open MetricCodes.Johnson.SpectralAsymptotics
namespace MetricCodes.Johnson.Rate
theorem _root_.solution
    {d : ℝ} (hd : 0 < d) (hdhalf : d < (1 : ℝ) / 2) :
    ∃ a u : ℝ, MetricCodes.Johnson.Feasible d a 0 0 u := by
  let a : ℝ := d / 2 + 1 / 4
  let u : ℝ := d / 4 + 1 / 4
  have ha : a < (1 : ℝ) / 2 := by
    dsimp [a]
    linarith
  have hu : 0 < u := by
    dsimp [u]
    linarith
  have hua : u < a := by
    dsimp [a, u]
    linarith
  have ha0 : 0 < a := lt_trans hu hua
  have hac : 0 < 1 - a := by linarith
  have hparams : MetricCodes.Johnson.AsymptoticParameters d a 0 0 u := by
    refine ⟨hd, hdhalf, ?_, ha, by norm_num, ?_, by norm_num,
      ?_, ?_, hua, ?_, ?_⟩
    · dsimp [a]
      linarith
    · linarith
    · linarith
    · simpa using hu
    · simpa using hua
    · norm_num
      linarith
  let A := a * (1 - a)
  let U := u * (1 - u)
  have hA : 0 < A := by
    dsimp [A]
    exact mul_pos ha0 hac
  have hs : 0 ≤ Real.sqrt U := Real.sqrt_nonneg _
  have hsden : 0 < 1 + 2 * Real.sqrt U := by positivity
  have hdiff : 2 * (A - U) < d := by
    dsimp [A, U, a, u]
    nlinarith [sq_nonneg d]
  have hinner : (A - U) / (1 + 2 * Real.sqrt U) < d / 2 := by
    apply (div_lt_iff₀ hsden).mpr
    nlinarith [mul_nonneg hd.le hs]
  have hquot :
      (A - U) / (A * (1 + 2 * Real.sqrt U)) < d / (2 * A) := by
    calc
      (A - U) / (A * (1 + 2 * Real.sqrt U)) =
          ((A - U) / (1 + 2 * Real.sqrt U)) / A := by
            field_simp [hA.ne', hsden.ne']

      _ < (d / 2) / A :=
        (div_lt_div_iff_of_pos_right hA).mpr hinner
      _ = d / (2 * A) := by ring_nf
  have hboundary :=
    MetricCodes.Johnson.spectralLimit_zero_fibre_boundary hu hua ha
  refine ⟨a, u, hparams, ?_⟩
  change MetricCodes.Johnson.asymptoticThreshold d a <
    MetricCodes.Johnson.spectralLimit a 0 0 u
  unfold MetricCodes.Johnson.asymptoticThreshold
  dsimp [A, U] at hquot
  have hquot' :
      (a * (1 - a) - u * (1 - u)) /
          (a * (1 - a) * (1 + 2 * Real.sqrt (u * (1 - u)))) <
        d / (2 * a * (1 - a)) := by
    convert hquot using 1 ; ring
  linarith
end MetricCodes.Johnson.Rate
