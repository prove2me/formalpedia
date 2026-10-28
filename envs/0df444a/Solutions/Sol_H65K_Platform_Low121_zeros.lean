-- Prove2me | solution 1 for H65K.Platform.Low121.zeros
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:37:52.948742+00:00
-- url     : https://prove2.me/submissions/67f24e73-274a-416e-996d-4cc4e29b0277

import Definitions.Def_ArdaRH65K_RS5_Band
import Theorems.Thm_Arb4_H1000_B03_0_ok
import Theorems.Thm_Arb4_H1000_B03_line
import Theorems.Thm_Arb4_H1000_B04_0_ok
import Theorems.Thm_Arb4_H1000_B04_line
import Theorems.Thm_Arb4_H1000_B05_0_ok
import Theorems.Thm_Arb4_H1000_B05_1_ok
import Theorems.Thm_Arb4_H1000_B05_2_ok
import Theorems.Thm_Arb4_H1000_B05_3_ok
import Theorems.Thm_Arb4_H1000_B06_0_ok
import Theorems.Thm_Arb4_H1000_B06_line
import Theorems.Thm_Arb4_H1000_B07_0_ok
import Theorems.Thm_Arb4_H1000_B07_line
import Theorems.Thm_Arb4_H1000_B08_0_ok
import Theorems.Thm_Arb4_H1000_B08_line
import Theorems.Thm_Arb4_H1000_B09_0_ok
import Theorems.Thm_Arb4_H1000_B09_line
import Theorems.Thm_Arb4_H1000_B10_0_ok
import Theorems.Thm_Arb4_H1000_B10_line
import Theorems.Thm_Arb4_H1000_B11_0_ok
import Theorems.Thm_Arb4_H1000_B11_line
import Theorems.Thm_Arb4_H1000_B12_0_ok
import Theorems.Thm_Arb4_H1000_B12_line
import Theorems.Thm_Arb4_H1000_B13_0_ok
import Theorems.Thm_Arb4_allC_append
import Theorems.Thm_Arb4_bandC_of
import Theorems.Thm_Arb4_bandC_sound
import Theorems.Thm_Arb4_ptCheckC_sound
import Theorems.Thm_RS5_BandZeros_glue
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Complex Arb4 Arb4.H1000 H1000Line
namespace H65K.Low121

noncomputable def first (xs : List PtD) : PtD := xs.getD 0 ⟨0, 0, 0, 0, 0, 0, 0, 0, false⟩

theorem first_checked (xs : List PtD) (hne : xs ≠ [])
    (h : xs.all (fun d => ptCheckC d.pt) = true) : ptCheckC (first xs).pt = true := by
  cases xs with
  | nil => contradiction
  | cons x xs =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    simpa [first] using h.1

theorem checked_nonzero (d : PtD) (h : ptCheckC d.pt = true) :
    completedRiemannZeta (1 / 2 + (tOf d.pt : ℂ) * I) ≠ 0 := by
  have hs := ptCheckC_sound d h
  have hg : XiLineZeros.gLine (tOf d.pt) ≠ 0 := by
    cases hp : d.pt.pos
    · have hneg := hs.2 hp
      linarith
    · have hpos := hs.1 hp
      linarith
  intro hz
  apply hg
  change (completedRiemannZeta (1 / 2 + (tOf d.pt : ℂ) * I)).re = 0
  rw [hz]
  rfl

theorem line_to_band {lo hi : ℝ} {K : ℕ}
    (line : ∃ xs : List ℝ, xs.length = K ∧ xs.IsChain (· < ·) ∧
      (∀ t ∈ xs, lo ≤ t ∧ t ≤ hi) ∧
      (∀ t ∈ xs, completedRiemannZeta (1 / 2 + (t : ℂ) * I) = 0))
    (hlo : completedRiemannZeta (1 / 2 + (lo : ℂ) * I) ≠ 0)
    (hhi : completedRiemannZeta (1 / 2 + (hi : ℂ) * I) ≠ 0) :
    RS5.BandZeros lo hi K := by
  obtain ⟨xs, hlen, hchain, hbd, hz⟩ := line
  refine ⟨xs, hlen, hchain, ?_, ?_⟩
  · intro t ht
    have h := hbd t ht
    have hzero := hz t ht
    have hne0 : lo ≠ t := by
      intro heq
      subst t
      exact hlo hzero
    have hne1 : t ≠ hi := by
      intro heq
      subst t
      exact hhi hzero
    exact ⟨lt_of_le_of_ne h.1 hne0, lt_of_le_of_ne h.2 hne1⟩
  · intro t ht
    have h := hz t ht
    have hne : (1 / 2 + (t : ℂ) * I) ≠ 0 := by
      intro heq
      have hre := congrArg Complex.re heq
      norm_num at hre
    have hzeta : riemannZeta (1 / 2 + (t : ℂ) * I) = 0 := by
      rw [riemannZeta_def_of_ne_zero hne, h, zero_div]
    exact ⟨h, hzeta⟩

theorem boundary03 :
    completedRiemannZeta (1 / 2 + ((121 : ℝ) : ℂ) * I) ≠ 0 := by
  have h := checked_nonzero (first B03_0)
    (first_checked B03_0 (by simp [B03_0]) B03_0_ok)
  have ht : tOf (first B03_0).pt = (121 : ℝ) := by
    norm_num [first, B03_0, PtD.pt, mkPt, tOf]
  simpa only [ht] using h

theorem boundary04 :
    completedRiemannZeta (1 / 2 + ((161 : ℝ) : ℂ) * I) ≠ 0 := by
  have h := checked_nonzero (first B04_0)
    (first_checked B04_0 (by simp [B04_0]) B04_0_ok)
  have ht : tOf (first B04_0).pt = (161 : ℝ) := by
    norm_num [first, B04_0, PtD.pt, mkPt, tOf]
  simpa only [ht] using h

theorem boundary05 :
    completedRiemannZeta (1 / 2 + ((201 : ℝ) : ℂ) * I) ≠ 0 := by
  have h := checked_nonzero (first B05_0)
    (first_checked B05_0 (by simp [B05_0]) B05_0_ok)
  have ht : tOf (first B05_0).pt = (201 : ℝ) := by
    norm_num [first, B05_0, PtD.pt, mkPt, tOf]
  simpa only [ht] using h

theorem boundary06 :
    completedRiemannZeta (1 / 2 + ((241 : ℝ) : ℂ) * I) ≠ 0 := by
  have h := checked_nonzero (first B06_0)
    (first_checked B06_0 (by simp [B06_0]) B06_0_ok)
  have ht : tOf (first B06_0).pt = (241 : ℝ) := by
    norm_num [first, B06_0, PtD.pt, mkPt, tOf]
  simpa only [ht] using h

theorem boundary07 :
    completedRiemannZeta (1 / 2 + ((281 : ℝ) : ℂ) * I) ≠ 0 := by
  have h := checked_nonzero (first B07_0)
    (first_checked B07_0 (by simp [B07_0]) B07_0_ok)
  have ht : tOf (first B07_0).pt = (281 : ℝ) := by
    norm_num [first, B07_0, PtD.pt, mkPt, tOf]
  simpa only [ht] using h

theorem boundary08 :
    completedRiemannZeta (1 / 2 + ((321 : ℝ) : ℂ) * I) ≠ 0 := by
  have h := checked_nonzero (first B08_0)
    (first_checked B08_0 (by simp [B08_0]) B08_0_ok)
  have ht : tOf (first B08_0).pt = (321 : ℝ) := by
    norm_num [first, B08_0, PtD.pt, mkPt, tOf]
  simpa only [ht] using h

theorem boundary09 :
    completedRiemannZeta (1 / 2 + ((361 : ℝ) : ℂ) * I) ≠ 0 := by
  have h := checked_nonzero (first B09_0)
    (first_checked B09_0 (by simp [B09_0]) B09_0_ok)
  have ht : tOf (first B09_0).pt = (361 : ℝ) := by
    norm_num [first, B09_0, PtD.pt, mkPt, tOf]
  simpa only [ht] using h

theorem boundary10 :
    completedRiemannZeta (1 / 2 + ((401 : ℝ) : ℂ) * I) ≠ 0 := by
  have h := checked_nonzero (first B10_0)
    (first_checked B10_0 (by simp [B10_0]) B10_0_ok)
  have ht : tOf (first B10_0).pt = (401 : ℝ) := by
    norm_num [first, B10_0, PtD.pt, mkPt, tOf]
  simpa only [ht] using h

theorem boundary11 :
    completedRiemannZeta (1 / 2 + ((441 : ℝ) : ℂ) * I) ≠ 0 := by
  have h := checked_nonzero (first B11_0)
    (first_checked B11_0 (by simp [B11_0]) B11_0_ok)
  have ht : tOf (first B11_0).pt = (441 : ℝ) := by
    norm_num [first, B11_0, PtD.pt, mkPt, tOf]
  simpa only [ht] using h

theorem boundary12 :
    completedRiemannZeta (1 / 2 + ((481 : ℝ) : ℂ) * I) ≠ 0 := by
  have h := checked_nonzero (first B12_0)
    (first_checked B12_0 (by simp [B12_0]) B12_0_ok)
  have ht : tOf (first B12_0).pt = (481 : ℝ) := by
    norm_num [first, B12_0, PtD.pt, mkPt, tOf]
  simpa only [ht] using h

theorem boundary13 :
    completedRiemannZeta (1 / 2 + ((520 : ℝ) : ℂ) * I) ≠ 0 := by
  have h := checked_nonzero (first B13_0)
    (first_checked B13_0 (by simp [B13_0]) B13_0_ok)
  have ht : tOf (first B13_0).pt = (520 : ℝ) := by
    norm_num [first, B13_0, PtD.pt, mkPt, tOf]
  simpa only [ht] using h

noncomputable def B05short : List PtD := B05_0 ++ B05_1 ++ B05_2 ++ B05_3.take 3
theorem B05last_checked : (B05_3.take 3).all (fun d => ptCheckC d.pt) = true := by
  apply List.all_eq_true.mpr
  intro d hd
  exact List.all_eq_true.mp B05_3_ok d (List.mem_of_mem_take hd)
theorem B05short_checked : B05short.all (fun d => ptCheckC d.pt) = true := by
  exact allC_append (allC_append (allC_append B05_0_ok B05_1_ok) B05_2_ok) B05last_checked
theorem B05short_band : H1000Line.bandOk 201 1 241 1 23 (B05short.map PtD.pt) = true := by
  decide +kernel
theorem B05short_line : ∃ xs : List ℝ, xs.length = 23 ∧ xs.IsChain (· < ·) ∧
    (∀ t ∈ xs, (201 : ℝ) ≤ t ∧ t ≤ (241 : ℝ)) ∧
    (∀ t ∈ xs, completedRiemannZeta (1 / 2 + (t : ℂ) * I) = 0) :=
  bandC_sound 201 241 201 1 241 1 23 (by norm_num) (by norm_num) B05short
    (bandC_of B05short_checked B05short_band)

theorem band03 : RS5.BandZeros 121 161 20 :=
  line_to_band B03_line boundary03 boundary04

theorem band04 : RS5.BandZeros 161 201 21 :=
  line_to_band B04_line boundary04 boundary05

theorem band05 : RS5.BandZeros 201 241 23 :=
  line_to_band B05short_line boundary05 boundary06

theorem band06 : RS5.BandZeros 241 281 24 :=
  line_to_band B06_line boundary06 boundary07

theorem band07 : RS5.BandZeros 281 321 24 :=
  line_to_band B07_line boundary07 boundary08

theorem band08 : RS5.BandZeros 321 361 26 :=
  line_to_band B08_line boundary08 boundary09

theorem band09 : RS5.BandZeros 361 401 26 :=
  line_to_band B09_line boundary09 boundary10

theorem band10 : RS5.BandZeros 401 441 27 :=
  line_to_band B10_line boundary10 boundary11

theorem band11 : RS5.BandZeros 441 481 27 :=
  line_to_band B11_line boundary11 boundary12

theorem band12 : RS5.BandZeros 481 520 27 :=
  line_to_band B12_line boundary12 boundary13

end H65K.Low121

open H65K.Low121 in
theorem solution : RS5.BandZeros 121 520 245 := by
  have h0 := band03
  have h1 := h0.glue (by norm_num) (by norm_num) band04
  have h2 := h1.glue (by norm_num) (by norm_num) band05
  have h3 := h2.glue (by norm_num) (by norm_num) band06
  have h4 := h3.glue (by norm_num) (by norm_num) band07
  have h5 := h4.glue (by norm_num) (by norm_num) band08
  have h6 := h5.glue (by norm_num) (by norm_num) band09
  have h7 := h6.glue (by norm_num) (by norm_num) band10
  have h8 := h7.glue (by norm_num) (by norm_num) band11
  have h9 := h8.glue (by norm_num) (by norm_num) band12
  exact h9
