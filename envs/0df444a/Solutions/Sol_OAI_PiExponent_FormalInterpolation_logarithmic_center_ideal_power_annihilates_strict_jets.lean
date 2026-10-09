-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmic_center_ideal_power_annihilates_strict_jets
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-08T17:11:44.318988+00:00
-- url     : https://prove2.me/submissions/864c9fc3-6cff-449b-bb65-bda3fc5b3ee6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmic_center_ideal_power_has_weighted_support

open Filter Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem solution
    {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ) (v : Fin (m + 1) → ℝ)
    (hv : ∀ i, 0 ≤ v i)
    (hT : ∀ i, v i.succ ≤ (T i : ℝ) * v 0)
    (R : ℝ) (he : ∀ i, R ≤ (e i : ℝ) * v i)
    (n : ℕ) (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hP : P ∈ FormalInterpolation.logarithmicCenterIdeal c T e ^ n)
    (a : { a // a ∈ strictWeightedSimplex v ((n : ℝ) * R) }) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector a.val)
      (FormalInterpolation.formalJet c P) = 0 := by
  have ha : a.val ∈ (realWeightedSimplex v ((n : ℝ) * R)).filter
      (fun b => ∑ i, v i * (b i : ℝ) < (n : ℝ) * R) := by
    simpa [strictWeightedSimplex] using a.property
  have hlt : ∑ i, v i * (a.val i : ℝ) < (n : ℝ) * R :=
    (Finset.mem_filter.mp ha).2
  by_contra hne
  have hweight :=
    OAI.PiExponent.FormalInterpolation.logarithmic_center_ideal_power_has_weighted_support
      c T e v hv hT R he n P hP a.val hne
  have hlt' : ∑ i, (a.val i : ℝ) * v i < (n : ℝ) * R := by
    simpa [mul_comm] using hlt
  exact (not_le_of_gt hlt') hweight
