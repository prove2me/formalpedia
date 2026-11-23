-- Prove2me | solution 2 for MultiIssueMediation.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T01:18:39.572849+00:00
-- url     : https://prove2.me/submissions/0be78515-7c33-4888-8095-69e378b7fe16
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MultiIssueMediation_AdjacentRule
import Theorems.Thm_MultiIssueMediation_part_i
import Theorems.Thm_MultiIssueMediation_part_ii
import Theorems.Thm_MultiIssueMediation_exists_precedence_order
import Theorems.Thm_MultiIssueMediation_adjacent_individuallyRational_efficient
import Theorems.Thm_MultiIssueMediation_adjacent_strategyProof

set_option autoImplicit false

open MultiIssueMediation

theorem solution {m : ℕ} (hm : 2 ≤ m) (f : MediationRule m) :
    Efficient f ∧ IndividuallyRational f ∧ StrategyProof f ↔ IsAdjacentRule f := by
  constructor
  · rintro ⟨hE, hIR, hSP⟩
    obtain ⟨y, hy, hoff⟩ := MultiIssueMediation.part_i hm f hE hIR hSP
    have hdiag := MultiIssueMediation.part_ii hm f hE hIR hSP
    obtain ⟨prec, hsto, -, hadj⟩ := MultiIssueMediation.exists_precedence_order hm f hE hIR hSP
    exact ⟨y, hy, prec, hsto, hoff, hdiag, hadj⟩
  · intro hf
    obtain ⟨hIR, hE⟩ := MultiIssueMediation.adjacent_individuallyRational_efficient hm f hf
    exact ⟨hE, hIR, MultiIssueMediation.adjacent_strategyProof hm f hf⟩
