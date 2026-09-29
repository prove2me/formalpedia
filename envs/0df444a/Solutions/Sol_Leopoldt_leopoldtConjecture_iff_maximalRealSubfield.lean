-- Prove2me | solution 1 for Leopoldt.leopoldtConjecture_iff_maximalRealSubfield
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T02:41:33.997244+00:00
-- url     : https://prove2.me/submissions/50a532b0-259a-4932-89a1-77e61c1f1fae

import Theorems.Thm_Leopoldt_defect_eq_defect_maximalRealSubfield

open NumberField

theorem solution (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCMField K] :
    Leopoldt.LeopoldtConjecture p K ↔ Leopoldt.LeopoldtConjecture p (maximalRealSubfield K) := by
  unfold Leopoldt.LeopoldtConjecture
  rw [Leopoldt.defect_eq_defect_maximalRealSubfield p K]
