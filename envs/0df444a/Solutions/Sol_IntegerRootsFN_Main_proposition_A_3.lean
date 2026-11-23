-- Prove2me | solution 1 for IntegerRootsFN.Main.proposition_A_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:15:55.296258+00:00
-- url     : https://prove2.me/submissions/52e3bfa8-639c-489d-b8bc-9482d8cdbcf6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_IntegerRootsFN_Main_Binary
import Definitions.Def_IntegerRootsFN_Main_ElementarySearch
import Theorems.Thm_IntegerRootsFN_Main_elementary_search_data
import Theorems.Thm_IntegerRootsFN_Main_elementary_search_runtime

set_option autoImplicit false

open IntegerRootsFN.Main

theorem solution :
    ∃ M : IntMul.MultitapeTM, ∃ C : ℝ, 0 < C ∧ ∃ k l : ℕ,
    ∀ (n b : ℕ) (f : Polynomial ℤ), Valid f n b →
      (∀ r : ℤ, f.IsRoot r → 2 ≤ |r| → r ∈ searchCandidates f n b) ∧
      (searchCandidates f n b).length ≤ 21 * min n b ∧
      (pointSize (searchCandidates f n b) : ℝ) ≤
        21 * (5 * (min n b : ℕ) + (b : ℝ) + (1 : ℝ) / 2 * logTwo ((min n b : ℕ) + 1)) ∧
      Runs M (polynomialWord (truncate f n b) (min n b) b)
        (integersWord (searchCandidates f n b))
        (softBound C k l (min n b) b ((min n b : ℕ) ^ 3 * (b : ℝ) ^ 2)) := by
  obtain ⟨M, C, hC, k, l, hrun⟩ := IntegerRootsFN.Main.elementary_search_runtime
  refine ⟨M, C, hC, k, l, ?_⟩
  intro n b f hf
  obtain ⟨hcov, hcard, hsize⟩ := IntegerRootsFN.Main.elementary_search_data n b f hf
  exact ⟨hcov, hcard, hsize, hrun n b f hf⟩