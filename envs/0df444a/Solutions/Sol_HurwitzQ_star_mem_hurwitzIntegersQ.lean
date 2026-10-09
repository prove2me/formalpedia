-- Prove2me | solution 1 for HurwitzQ.star_mem_hurwitzIntegersQ
-- status  : ACCEPTED   (prove)
-- author  : @jawneeboy
-- created : 2026-09-18T18:10:21.072912+00:00
-- url     : https://prove2.me/submissions/4d222391-07ed-490e-a08d-30b6a813909e

import Definitions.Def_HurwitzQ_hurwitzIntegersQ
import Mathlib.Algebra.Quaternion
import Mathlib.Tactic.Ring

open Quaternion

open HurwitzQ


theorem solution {q : ℍ[ℚ]} (hq : q ∈ hurwitzIntegersQ) :
    star q ∈ hurwitzIntegersQ := by
  rcases hq with ⟨a, b, c, d, hqa, hqi, hqj, hqk⟩ | ⟨a, b, c, d, hqa, hqi, hqj, hqk⟩
  · refine .inl ⟨a, -b, -c, -d, ?_, ?_, ?_, ?_⟩ <;>
      simp only [re_star, imI_star, imJ_star, imK_star, hqa, hqi, hqj, hqk] <;>
      push_cast <;> ring
  · refine .inr ⟨a, -b - 1, -c - 1, -d - 1, ?_, ?_, ?_, ?_⟩ <;>
      simp only [re_star, imI_star, imJ_star, imK_star, hqa, hqi, hqj, hqk] <;>
      push_cast <;> ring


