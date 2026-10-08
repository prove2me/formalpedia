-- Prove2me | solution 1 for MethanolMuDrift.allLine_fit
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:18:52.30324+00:00
-- url     : https://prove2.me/submissions/7328b20d-9caa-4393-8afb-304e209bd236

import Mathlib
import Definitions.Def_Bagdonaite2013_MethanolMuDrift

namespace MethanolMuDrift.Pb501478e

open MethanolMuDrift

lemma hS : wSum allSigma = 8870581000/74701449 := by
  simp [wSum, allSigma, Fin.sum_univ_four]; norm_num

lemma hSK : wSumK allK allSigma = -16748083000/74701449 := by
  simp [wSumK, allK, allSigma, Fin.sum_univ_four]; norm_num

lemma hSV : wSumV allV allSigma = 25266018964/24900483 := by
  simp [wSumV, allV, allSigma, Fin.sum_univ_four]; norm_num

lemma hSKK : wSumKK allK allSigma = 209454283000/74701449 := by
  simp [wSumKK, allK, allSigma, Fin.sum_univ_four]; norm_num

lemma hSKV : wSumKV allK allV allSigma = -49719728764/24900483 := by
  simp [wSumKV, allK, allV, allSigma, Fin.sum_univ_four]; norm_num

lemma est : |muDriftEstimate allK allV allSigma - 11.0e-8| ≤ 0.5e-8 := by
  simp only [muDriftEstimate, wlsSlope, wlsDet, hS, hSK, hSV, hSKK, hSKV, speedOfLight]
  rw [abs_le]; constructor <;> norm_num

lemma stat : |muDriftStatErr allK allSigma - 6.8e-8| ≤ 0.1e-8 := by
  simp only [muDriftStatErr, wlsSlopeStdErr, wlsDet, hS, hSK, hSKK, speedOfLight]
  have h1 : (0.0204:ℝ) ≤ Real.sqrt ((8870581000/74701449) / ((8870581000/74701449) * (209454283000/74701449)
        - (-16748083000/74701449) ^ 2)) := by
    apply Real.le_sqrt_of_sq_le; norm_num
  have h2 : Real.sqrt ((8870581000/74701449) / ((8870581000/74701449) * (209454283000/74701449)
        - (-16748083000/74701449) ^ 2)) ≤ 0.0206 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  rw [abs_le]; constructor
  · rw [le_sub_iff_add_le, le_div_iff₀ (by norm_num)]; nlinarith
  · rw [sub_le_iff_le_add, div_le_iff₀ (by norm_num)]; nlinarith

lemma chi : |wlsReducedChiSq allK allV allSigma - 6.4| ≤ 0.2 := by
  have hb : wlsSlope allK allV allSigma = ((8870581000/74701449) * (-49719728764/24900483)
      - (-16748083000/74701449) * (25266018964/24900483)) /
      ((8870581000/74701449) * (209454283000/74701449) - (-16748083000/74701449) ^ 2) := by
    simp only [wlsSlope, wlsDet, hS, hSK, hSV, hSKK, hSKV]
  have ha : wlsIntercept allK allV allSigma = ((209454283000/74701449) * (25266018964/24900483)
      - (-16748083000/74701449) * (-49719728764/24900483)) /
      ((8870581000/74701449) * (209454283000/74701449) - (-16748083000/74701449) ^ 2) := by
    simp only [wlsIntercept, wlsDet, hS, hSK, hSV, hSKK, hSKV]
  simp only [wlsReducedChiSq, wlsChiSq, ha, hb, Fin.sum_univ_four]
  simp [allK, allV, allSigma]
  rw [abs_le]; constructor <;> norm_num

end MethanolMuDrift.Pb501478e

open MethanolMuDrift in
theorem solution :
    |muDriftEstimate allK allV allSigma - 11.0e-8| ≤ 0.5e-8 ∧
      |muDriftStatErr allK allSigma - 6.8e-8| ≤ 0.1e-8 ∧
      |wlsReducedChiSq allK allV allSigma - 6.4| ≤ 0.2 := by
  exact ⟨MethanolMuDrift.Pb501478e.est, MethanolMuDrift.Pb501478e.stat, MethanolMuDrift.Pb501478e.chi⟩
