-- Prove2me | solution 1 for MethanolMuDrift.eLine_fit
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:47:47.072964+00:00
-- url     : https://prove2.me/submissions/cd8eff4d-cec9-418e-aac6-8d21b8940595

import Mathlib
import Definitions.Def_Bagdonaite2013_MethanolMuDrift

namespace MethanolMuDrift.P66886b80

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

lemma est : |muDriftEstimate eK eV eSigma - (-0.1e-8)| ≤ 0.05e-8 := by
  simp only [muDriftEstimate, wlsSlope, wlsDet, hS, hSK, hSV, hSKK, hSKV, speedOfLight]
  rw [abs_le]; constructor <;> norm_num

lemma stat : |muDriftStatErr eK eSigma - 7.6e-8| ≤ 0.1e-8 := by
  simp only [muDriftStatErr, wlsSlopeStdErr, wlsDet, hS, hSK, hSKK, speedOfLight]
  have h1 : (0.0225:ℝ) ≤ Real.sqrt ((1400436100/74701449) / ((1400436100/74701449) * (201984138100/74701449)
        - (-9277938100/74701449) ^ 2)) := by
    apply Real.le_sqrt_of_sq_le; norm_num
  have h2 : Real.sqrt ((1400436100/74701449) / ((1400436100/74701449) * (201984138100/74701449)
        - (-9277938100/74701449) ^ 2)) ≤ 0.02308 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  rw [abs_le]; constructor
  · rw [le_sub_iff_add_le, le_div_iff₀ (by norm_num)]; nlinarith
  · rw [sub_le_iff_le_add, div_le_iff₀ (by norm_num)]; nlinarith

lemma chi : |wlsReducedChiSq eK eV eSigma - 2.0| ≤ 0.05 := by
  have hb : wlsSlope eK eV eSigma = ((1400436100/74701449) * (-28803323044/24900483)
      - (-9277938100/74701449) * (4349613244/24900483)) /
      ((1400436100/74701449) * (201984138100/74701449) - (-9277938100/74701449) ^ 2) := by
    simp only [wlsSlope, wlsDet, hS, hSK, hSV, hSKK, hSKV]
  have ha : wlsIntercept eK eV eSigma = ((201984138100/74701449) * (4349613244/24900483)
      - (-9277938100/74701449) * (-28803323044/24900483)) /
      ((1400436100/74701449) * (201984138100/74701449) - (-9277938100/74701449) ^ 2) := by
    simp only [wlsIntercept, wlsDet, hS, hSK, hSV, hSKK, hSKV]
  simp only [wlsReducedChiSq, wlsChiSq, ha, hb, Fin.sum_univ_three]
  simp [eK, eV, eSigma]
  rw [abs_le]; constructor <;> norm_num

end MethanolMuDrift.P66886b80

open MethanolMuDrift in
theorem solution :
    |muDriftEstimate eK eV eSigma - (-0.1e-8)| ≤ 0.05e-8 ∧
      |muDriftStatErr eK eSigma - 7.6e-8| ≤ 0.1e-8 ∧
      |wlsReducedChiSq eK eV eSigma - 2.0| ≤ 0.05 := by
  exact ⟨MethanolMuDrift.P66886b80.est, MethanolMuDrift.P66886b80.stat, MethanolMuDrift.P66886b80.chi⟩
