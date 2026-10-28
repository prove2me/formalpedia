-- Prove2me | solution 2 for McFadden1974.QPTest.axiom6_iff_qp_min_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T11:47:53.914253+00:00
-- url     : https://prove2.me/submissions/efdce8ee-364d-48a9-bb21-09d05f072de2

import Mathlib
import Definitions.Def_McFadden1974_QPTest_ChoiceData
import Theorems.Thm_McFadden1974_QPTest_interior_gives_positive_coefficients
import Theorems.Thm_McFadden1974_QPTest_noninterior_gives_separator
import Theorems.Thm_McFadden1974_QPTest_zero_min_implies_axiom6

-- carved verbatim out of submission 4959f893-fea1-4640-b82e-cc4539818966, lines 165-170

section
set_option autoImplicit false
open McFadden1974
open McFadden1974.QPTest

theorem goal_core {N K : ℕ} (d : ChoiceData N K)
    (h5 : d.Axiom5) :
    d.Axiom6 ↔
      IsLeast ((fun y : EuclideanSpace ℝ (Fin K) => ‖y‖ ^ 2) '' d.qpFeasible) 0 := by
  constructor
  · intro h6
    by_cases hi : (0 : EuclideanSpace ℝ (Fin K)) ∈ interior d.coneSet
    · exact (McFadden1974.QPTest.interior_gives_positive_coefficients d hi).2
    · exact absurd h6 (McFadden1974.QPTest.noninterior_gives_separator d hi).2
  · rintro ⟨⟨y, hy, hy0⟩, _⟩
    have : y = 0 := by simpa using hy0
    subst this
    exact McFadden1974.QPTest.zero_min_implies_axiom6 d h5 hy

end

section
set_option autoImplicit false
open McFadden1974.QPTest

theorem solution {N K : ℕ} (d : ChoiceData N K)
    (h5 : d.Axiom5) :
    d.Axiom6 ↔
      IsLeast ((fun y : EuclideanSpace ℝ (Fin K) => ‖y‖ ^ 2) '' d.qpFeasible) 0 := by
  exact goal_core d h5

end
