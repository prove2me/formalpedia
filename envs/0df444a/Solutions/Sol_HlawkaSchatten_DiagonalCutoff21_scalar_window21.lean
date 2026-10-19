-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff21.scalar_window21
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-17T09:37:56.795031+00:00
-- url     : https://prove2.me/submissions/af4fc091-6e07-4111-a6ad-25ece6a64a27

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_lower21_chunk00
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_lower21_chunk01
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_lower21_chunk02
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_lower21_chunk03
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_lower21_chunk04
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_lower21_chunk05
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_lower21_chunk06
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_lower21_chunk07
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_lower21_chunk08
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_lower21_chunk09
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_envelope_linear21
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_cyclicConstant_upper21

open HlawkaSchatten.DiagonalConstruction

theorem solution :
    ∀ p : ℝ, 21 ≤ p → p ≤ 26 →
      (273 / 625 : ℝ) * p < cyclicConstant p ∧
      cyclicConstant p ≤ p / 2 ∧
      scalarEnvelope p (1011 / 2500 : ℝ) < cyclicConstant p := by
  intro p hp hpmax
  have hlower : (273/625 : ℝ)*p < cyclicConstant p := by
    rcases le_total p (47/2 : ℝ) with hl | hr
    ·
      rcases le_total p (22 : ℝ) with hal | har
      ·
        rcases le_total p (43/2 : ℝ) with haal | haar
        ·
          exact HlawkaSchatten.DiagonalCutoff21.lower21_chunk00 p hp haal
        ·
          exact HlawkaSchatten.DiagonalCutoff21.lower21_chunk01 p haar hal
      ·
        rcases le_total p (45/2 : ℝ) with habl | habr
        ·
          exact HlawkaSchatten.DiagonalCutoff21.lower21_chunk02 p har habl
        ·
          rcases le_total p (23 : ℝ) with habbl | habbr
          ·
            exact HlawkaSchatten.DiagonalCutoff21.lower21_chunk03 p habr habbl
          ·
            exact HlawkaSchatten.DiagonalCutoff21.lower21_chunk04 p habbr hl
    ·
      rcases le_total p (49/2 : ℝ) with hbl | hbr
      ·
        rcases le_total p (24 : ℝ) with hbal | hbar
        ·
          exact HlawkaSchatten.DiagonalCutoff21.lower21_chunk05 p hr hbal
        ·
          exact HlawkaSchatten.DiagonalCutoff21.lower21_chunk06 p hbar hbl
      ·
        rcases le_total p (25 : ℝ) with hbbl | hbbr
        ·
          exact HlawkaSchatten.DiagonalCutoff21.lower21_chunk07 p hbr hbbl
        ·
          rcases le_total p (51/2 : ℝ) with hbbbl | hbbbr
          ·
            exact HlawkaSchatten.DiagonalCutoff21.lower21_chunk08 p hbbr hbbbl
          ·
            exact HlawkaSchatten.DiagonalCutoff21.lower21_chunk09 p hbbbr hpmax
  refine ⟨hlower, ?_, ?_⟩
  · exact HlawkaSchatten.DiagonalCutoff21.cyclicConstant_upper21 (by linarith) (by linarith)
  · exact (HlawkaSchatten.DiagonalCutoff21.envelope_linear21 hp).trans hlower

#print axioms solution
