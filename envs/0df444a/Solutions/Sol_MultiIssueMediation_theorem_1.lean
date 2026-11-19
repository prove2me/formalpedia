-- Prove2me | solution 1 for MultiIssueMediation.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T06:18:59.364672+00:00
-- url     : https://prove2.me/submissions/387231ec-6490-40ad-9f70-3f988ae79a6f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MultiIssueMediation_AdjacentRule
import Theorems.Thm_MultiIssueMediation_part_i
import Theorems.Thm_MultiIssueMediation_part_ii
import Theorems.Thm_MultiIssueMediation_exists_precedence_order
import Theorems.Thm_MultiIssueMediation_adjacent_individuallyRational_efficient
import Theorems.Thm_MultiIssueMediation_adjacent_strategyProof

open MultiIssueMediation

theorem solution {m : ℕ} (hm : 2 ≤ m) (f : MediationRule m) :
    Efficient f ∧ IndividuallyRational f ∧ StrategyProof f ↔ IsAdjacentRule f := by
  constructor
  · rintro ⟨hE, hIR, hSP⟩
    obtain ⟨y, hy, hup⟩ := part_i hm f hE hIR hSP
    obtain ⟨prec, hprec, -, hadj⟩ := exists_precedence_order hm f hE hIR hSP
    exact ⟨y, hy, prec, hprec, hup, fun k => part_ii hm f hE hIR hSP k, hadj⟩
  · intro hf
    obtain ⟨hIR, hE⟩ := adjacent_individuallyRational_efficient hm f hf
    exact ⟨hE, hIR, adjacent_strategyProof hm f hf⟩
