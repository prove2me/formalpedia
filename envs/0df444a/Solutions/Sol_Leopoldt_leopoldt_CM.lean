-- Prove2me | solution 1 for Leopoldt.leopoldt_CM
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-09T14:45:40.886986+00:00
-- url     : https://prove2.me/submissions/a4b610b1-f4de-43cc-b596-6471b6d210ec
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Leopoldt_defect_maximalRealSubfield_pos_of_defect_pos
import Theorems.Thm_Leopoldt_leopoldt_totallyReal

open NumberField

/-- Theorem 1 of the source, reduced along the CM/totally real boundary of Section 1.1, p. 4:
a positive Leopoldt defect of a CM field forces a positive defect for its maximal real subfield,
and Leopoldt's conjecture for totally real fields says that cannot happen. -/
theorem solution (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (K : Type*) [Field K] [NumberField K] [IsCMField K] :
    Leopoldt.LeopoldtConjecture p K := by
  by_contra h
  -- Were the conjecture to fail for `K`, its defect would be positive.
  have hpos : 0 < Leopoldt.defect p K := Nat.pos_of_ne_zero h
  -- Then the defect of the maximal real subfield `K⁺` would be positive as well.
  have h1 := Leopoldt.defect_maximalRealSubfield_pos_of_defect_pos p hp K hpos
  -- But `K⁺` is totally real, so its defect vanishes.
  have h2 : Leopoldt.defect p (maximalRealSubfield K) = 0 :=
    Leopoldt.leopoldt_totallyReal p hp (maximalRealSubfield K)
  omega
