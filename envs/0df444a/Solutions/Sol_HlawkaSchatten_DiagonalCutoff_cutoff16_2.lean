-- Prove2me | solution 2 for HlawkaSchatten.DiagonalCutoff.cutoff16
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:17:16.095185+00:00
-- url     : https://prove2.me/submissions/d3429290-96f6-4f3a-b4f5-4bc2e888cd62

import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_campaign_cutoff21
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_complex_least_of_real_three
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_window00
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_window01
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_window02
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_window03
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_window04
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_window05
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_window06
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_window07
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_window08
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_window09
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_window10
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_window11
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_window12
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_window13
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_window14
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_window15
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_window16
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_window17
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_window18
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_window19
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_window20
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_window21
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_window22
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_window23
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_window24
import Mathlib.Tactic.Linarith
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem solution :
    ∀ p : ℝ, 16 ≤ p →
      IsLeast {C : ℝ | ∀ n : ℕ,
        HasHlawkaConstant (lpNorm p : (Fin n → ℂ) → ℝ) C}
        (cyclicConstant p) := by
  intro p hp16
  by_cases hp21 : 21 ≤ p
  · exact campaign_cutoff21 p hp21
  apply HlawkaSchatten.DiagonalCutoff21.complex_least_of_real_three p (by linarith)
  by_cases h0 : p ≤ (513/32 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_window00 p (by linarith) h0
  by_cases h1 : p ≤ (257/16 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_window01 p (by linarith) h1
  by_cases h2 : p ≤ (515/32 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_window02 p (by linarith) h2
  by_cases h3 : p ≤ (129/8 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_window03 p (by linarith) h3
  by_cases h4 : p ≤ (517/32 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_window04 p (by linarith) h4
  by_cases h5 : p ≤ (259/16 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_window05 p (by linarith) h5
  by_cases h6 : p ≤ (519/32 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_window06 p (by linarith) h6
  by_cases h7 : p ≤ (65/4 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_window07 p (by linarith) h7
  by_cases h8 : p ≤ (261/16 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_window08 p (by linarith) h8
  by_cases h9 : p ≤ (131/8 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_window09 p (by linarith) h9
  by_cases h10 : p ≤ (263/16 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_window10 p (by linarith) h10
  by_cases h11 : p ≤ (33/2 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_window11 p (by linarith) h11
  by_cases h12 : p ≤ (133/8 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_window12 p (by linarith) h12
  by_cases h13 : p ≤ (67/4 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_window13 p (by linarith) h13
  by_cases h14 : p ≤ (135/8 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_window14 p (by linarith) h14
  by_cases h15 : p ≤ (17 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_window15 p (by linarith) h15
  by_cases h16 : p ≤ (69/4 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_window16 p (by linarith) h16
  by_cases h17 : p ≤ (35/2 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_window17 p (by linarith) h17
  by_cases h18 : p ≤ (71/4 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_window18 p (by linarith) h18
  by_cases h19 : p ≤ (18 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_window19 p (by linarith) h19
  by_cases h20 : p ≤ (37/2 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_window20 p (by linarith) h20
  by_cases h21 : p ≤ (19 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_window21 p (by linarith) h21
  by_cases h22 : p ≤ (39/2 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_window22 p (by linarith) h22
  by_cases h23 : p ≤ (20 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_window23 p (by linarith) h23
  exact HlawkaSchatten.DiagonalCutoff16.real_three_window24 p (by linarith) (by linarith)
