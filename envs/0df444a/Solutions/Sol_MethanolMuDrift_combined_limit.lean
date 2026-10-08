-- Prove2me | solution 1 for MethanolMuDrift.combined_limit
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:04:51.475205+00:00
-- url     : https://prove2.me/submissions/09c6f0c8-3372-48bb-a625-f2f589d7d90e

import Mathlib
import Definitions.Def_Bagdonaite2013_MethanolMuDrift

namespace MethanolMuDrift.P5c849c92

open MethanolMuDrift

lemma hS : wSum eSigma = 1400436100/74701449 := by
  simp [wSum, eSigma, Fin.sum_univ_three]; norm_num

lemma hSK : wSumK eK eSigma = -9277938100/74701449 := by
  simp [wSumK, eK, eSigma, Fin.sum_univ_three]; norm_num

lemma hSV : wSumV eV eSigma = 4349613244/24900483 := by
  simp [wSumV, eV, eSigma, Fin.sum_univ_three]; norm_num

lemma hSKK : wSumKK eK eSigma = 201984138100/74701449 := by
  simp [wSumKK, eK, eSigma, Fin.sum_univ_three]; norm_num

lemma hSKV : wSumKV eK eV eSigma = -28803323044/24900483 := by
  simp [wSumKV, eK, eV, eSigma, Fin.sum_univ_three]; norm_num

lemma est : |muDriftEstimate eK eV eSigma| < 0.05e-7 := by
  simp only [muDriftEstimate, wlsSlope, wlsDet, hS, hSK, hSV, hSKK, hSKV, speedOfLight]
  rw [abs_lt]; constructor <;> norm_num

lemma statsq : muDriftStatErr eK eSigma ^ 2
    = (1400436100/74701449) / ((1400436100/74701449) * (201984138100/74701449)
        - (-9277938100/74701449) ^ 2) / (299792.458:ℝ) ^ 2 := by
  simp only [muDriftStatErr, wlsSlopeStdErr, wlsDet, hS, hSK, hSKK, speedOfLight]
  rw [div_pow, Real.sq_sqrt (by norm_num)]

lemma tot : |Real.sqrt (muDriftStatErr eK eSigma ^ 2 + muDriftSysErr ^ 2) - 1.0e-7| < 0.05e-7 := by
  rw [statsq, muDriftSysErr, abs_lt]
  constructor
  · have : (0.95e-7:ℝ) < Real.sqrt ((1400436100/74701449) / ((1400436100/74701449) * (201984138100/74701449)
        - (-9277938100/74701449) ^ 2) / (299792.458:ℝ) ^ 2 + (7.0e-8:ℝ) ^ 2) := by
      rw [Real.lt_sqrt (by norm_num)]; norm_num
    linarith
  · have : Real.sqrt ((1400436100/74701449) / ((1400436100/74701449) * (201984138100/74701449)
        - (-9277938100/74701449) ^ 2) / (299792.458:ℝ) ^ 2 + (7.0e-8:ℝ) ^ 2) < 1.05e-7 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    linarith

end MethanolMuDrift.P5c849c92

open MethanolMuDrift in
theorem solution :
    |muDriftEstimate eK eV eSigma| < 0.05e-7 ∧
      |Real.sqrt (muDriftStatErr eK eSigma ^ 2 + muDriftSysErr ^ 2) - 1.0e-7| < 0.05e-7 := by
  exact ⟨MethanolMuDrift.P5c849c92.est, MethanolMuDrift.P5c849c92.tot⟩
