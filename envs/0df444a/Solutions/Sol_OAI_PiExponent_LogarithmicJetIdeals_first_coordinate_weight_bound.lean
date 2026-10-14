-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.first_coordinate_weight_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T10:31:05.52606+00:00
-- url     : https://prove2.me/submissions/7c3e874f-4af2-4805-beff-a10e144db60a

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem solution
    {m : ℕ} (v0 theta : ℝ) (w : Fin m → ℝ)
    (R : ℝ) (e : Fin (m + 1) → ℕ)
    (hv0 : 0 < v0) (htheta : 0 < theta) (hw : ∀ i, 0 < w i)
    (he : ∀ i, R ≤ (e i : ℝ) * InterpolationMatrix.rowWeights v0 theta w i)
    (b : Fin (m + 1) → ℕ)
    (hb : (∑ j, InterpolationMatrix.rowWeights v0 theta w j * (b j : ℝ)) < R) :
    b (0 : Fin (m + 1)) < e (0 : Fin (m + 1)) := by
  by_contra hnot
  have hbe : (e (0 : Fin (m + 1)) : ℝ) ≤ (b (0 : Fin (m + 1)) : ℝ) := by
    exact_mod_cast Nat.le_of_not_gt hnot
  have hweights : ∀ j : Fin (m + 1),
      0 < InterpolationMatrix.rowWeights v0 theta w j := by
    intro j
    refine Fin.cases ?_ ?_ j
    · simpa [InterpolationMatrix.rowWeights] using hv0
    · intro i
      simpa [InterpolationMatrix.rowWeights] using div_pos (hw i) htheta
  have hnonneg : ∀ j : Fin (m + 1),
      0 ≤ InterpolationMatrix.rowWeights v0 theta w j * (b j : ℝ) := by
    intro j
    exact mul_nonneg (hweights j).le (Nat.cast_nonneg _)
  have hterm :
      InterpolationMatrix.rowWeights v0 theta w (0 : Fin (m + 1)) *
          (b (0 : Fin (m + 1)) : ℝ) ≤
        ∑ j, InterpolationMatrix.rowWeights v0 theta w j * (b j : ℝ) :=
    Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ _)
  have hmul :
      (e (0 : Fin (m + 1)) : ℝ) * v0 ≤
        (b (0 : Fin (m + 1)) : ℝ) * v0 :=
    mul_le_mul_of_nonneg_right hbe hv0.le
  have hRterm :
      R ≤ InterpolationMatrix.rowWeights v0 theta w (0 : Fin (m + 1)) *
          (b (0 : Fin (m + 1)) : ℝ) := by
    calc
      R ≤ (e (0 : Fin (m + 1)) : ℝ) * v0 := by
        simpa [InterpolationMatrix.rowWeights] using he (0 : Fin (m + 1))
      _ ≤ InterpolationMatrix.rowWeights v0 theta w (0 : Fin (m + 1)) *
          (b (0 : Fin (m + 1)) : ℝ) := by
        simpa [InterpolationMatrix.rowWeights, mul_comm] using hmul
  have hRsum :
      R ≤ ∑ j, InterpolationMatrix.rowWeights v0 theta w j * (b j : ℝ) :=
    hRterm.trans hterm
  linarith