-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff21.scalar_window26
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-17T09:37:57.723082+00:00
-- url     : https://prove2.me/submissions/31e53398-4398-494e-a2f2-85f9cfdba2f9

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_lower26_chunk00
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_lower26_chunk01
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_lower26_chunk02
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_lower26_chunk03
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_lower26_chunk04
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_lower26_chunk05
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_envelope_linear26
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_cyclicConstant_upper21

open HlawkaSchatten.DiagonalConstruction

theorem solution :
    ∀ p : ℝ, 26 ≤ p → p ≤ 32 →
      (443 / 1000 : ℝ) * p < cyclicConstant p ∧
      cyclicConstant p ≤ p / 2 ∧
      scalarEnvelope p (197 / 500 : ℝ) < cyclicConstant p := by
  intro p hp hpmax
  have hlower : (443/1000 : ℝ)*p < cyclicConstant p := by
    rcases le_total p (29 : ℝ) with hl | hr
    ·
      rcases le_total p (27 : ℝ) with hal | har
      ·
        exact HlawkaSchatten.DiagonalCutoff21.lower26_chunk00 p hp hal
      ·
        rcases le_total p (28 : ℝ) with habl | habr
        ·
          exact HlawkaSchatten.DiagonalCutoff21.lower26_chunk01 p har habl
        ·
          exact HlawkaSchatten.DiagonalCutoff21.lower26_chunk02 p habr hl
    ·
      rcases le_total p (30 : ℝ) with hbl | hbr
      ·
        exact HlawkaSchatten.DiagonalCutoff21.lower26_chunk03 p hr hbl
      ·
        rcases le_total p (31 : ℝ) with hbbl | hbbr
        ·
          exact HlawkaSchatten.DiagonalCutoff21.lower26_chunk04 p hbr hbbl
        ·
          exact HlawkaSchatten.DiagonalCutoff21.lower26_chunk05 p hbbr hpmax
  refine ⟨hlower, ?_, ?_⟩
  · exact HlawkaSchatten.DiagonalCutoff21.cyclicConstant_upper21 (by linarith) (by linarith)
  · exact (HlawkaSchatten.DiagonalCutoff21.envelope_linear26 hp).trans hlower

#print axioms solution
