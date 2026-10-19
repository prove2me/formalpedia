-- Prove2me | solution 1 for MetricCodes.Johnson.Rate.binaryRate_le_shellRate_of_projectionGrams
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:31.72047+00:00
-- url     : https://prove2.me/submissions/8b4d6a71-574e-4a48-9ecd-3ca0780fef41

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_threshold_lt_one
import Theorems.Thm_MetricCodes_Hamming_ceil_distance_pos
import Theorems.Thm_MetricCodes_Hamming_spectralGap_pos
import Theorems.Thm_MetricCodes_Johnson_binaryCodeNumber_eq_hamming
import Theorems.Thm_MetricCodes_Johnson_threshold_lt_one
import Theorems.Thm_MetricCodes_Johnson_finite_binaryCodeNumber_bound_of_projection_gram
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_eventually_admissibleDegrees
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_binaryRate_le_shellRate_of_eventually
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_spectralGap_pos
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_eventually_spectralGap_lt
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_asymptoticThreshold_lt_one
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_eventually_one_sub_threshold_lt
import Theorems.Thm_MetricCodes_Johnson_Rate_certificateConstant_pos

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
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.Feasible d a b g u)
    (hdata : ∀ᶠ n : ℕ in atTop,
      Nonempty
        (MetricCodes.Johnson.ProjectionGram n (shellWeight a n)
          (supportDegree b n) (complementDegree g n)
          (terminalDegree u n))) :
    MetricCodes.Hamming.binaryRate d ≤ MetricCodes.Johnson.shellRate a b g u := by
  apply MetricCodes.Johnson.Asymptotics.binaryRate_le_shellRate_of_eventually
    h.1 (certificateConstant_pos h)
  filter_upwards [hdata, eventually_admissibleDegrees h.1,
    eventually_spectralGap_lt h,
    eventually_one_sub_threshold_lt h.1,
    eventually_gt_atTop (0 : ℕ)]
    with n hnonempty hadmissible hgap hnumerator hn
  obtain ⟨data⟩ := hnonempty
  let t := MetricCodes.Johnson.threshold n (shellWeight a n)
    (Nat.ceil (d * (n : ℝ)))
  let lam := MetricCodes.Johnson.topEigenvalue n (shellWeight a n)
    (supportDegree b n) (complementDegree g n)
    (terminalDegree u n)
  let G := spectralGap d a b g u
  let B := 2 - MetricCodes.Johnson.asymptoticThreshold d a
  have hd := MetricCodes.Hamming.ceil_distance_pos h.1.distance_pos hn
  have hG : 0 < G := spectralGap_pos h
  have hB : 0 < B := by
    dsimp [B]
    linarith [asymptoticThreshold_lt_one h.1]
  have hden : 0 < lam - t := by
    dsimp [lam, t, G] at hgap ⊢
    linarith [spectralGap_pos h]
  have ht : 0 < 1 - t := by
    dsimp [t]
    exact sub_pos.mpr
      (MetricCodes.Johnson.threshold_lt_one hadmissible.weight_pos
        hadmissible.weight_lt hd)
  have hratio : (1 - t) / (lam - t) ≤ B / G := by
    apply (div_le_div_iff₀ hden hG).mpr
    calc
      (1 - t) * G ≤ B * G := by
        apply mul_le_mul_of_nonneg_right _ hG.le
        exact le_of_lt hnumerator
      _ ≤ B * (lam - t) := by
        apply mul_le_mul_of_nonneg_left _ hB.le
        exact le_of_lt hgap
  have hfactor : 0 ≤ bassalygoFactor a n := by
    unfold bassalygoFactor
    exact div_nonneg (by positivity) (Nat.cast_nonneg _)
  have hwindow : 0 ≤ windowFibreQuotient a b g u n := by
    unfold windowFibreQuotient
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hfinite :=
    MetricCodes.Johnson.finite_binaryCodeNumber_bound_of_projection_gram
      hadmissible hd data (sub_pos.mp hden)
  rw [MetricCodes.Johnson.binaryCodeNumber_eq_hamming] at hfinite
  change
    (MetricCodes.Hamming.codeNumber n
      (Nat.ceil (d * (n : ℝ))) : ℝ) ≤
      bassalygoFactor a n *
        (((1 - t) / (lam - t)) * windowFibreQuotient a b g u n)
    at hfinite
  calc
    (MetricCodes.Hamming.codeNumber n
      (Nat.ceil (d * (n : ℝ))) : ℝ) ≤
        bassalygoFactor a n *
          (((1 - t) / (lam - t)) * windowFibreQuotient a b g u n) :=
      hfinite
    _ ≤ bassalygoFactor a n *
          ((B / G) * windowFibreQuotient a b g u n) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hratio hwindow) hfactor
    _ = certificateConstant d a b g u *
          bassalygoWindowFibreQuotient a b g u n := by
      unfold certificateConstant bassalygoWindowFibreQuotient
      dsimp [B, G]
      ring
end MetricCodes.Johnson.Rate
