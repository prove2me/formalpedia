-- Prove2me | solution 1 for HurwitzQ.lift_mem_hurwitzIntegers
-- status  : ACCEPTED   (prove)
-- author  : @jawneeboy
-- created : 2026-09-18T18:10:08.709145+00:00
-- url     : https://prove2.me/submissions/903f73ad-d4c5-48a6-8507-71e7c0e057ab

import Definitions.Def_HurwitzQ_hurwitzIntegersQ
import Definitions.Def_Quaternion_hurwitzIntegers
import Definitions.Def_Quaternion_lipschitzIntegers
import Mathlib.Algebra.Quaternion
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Quaternion

open HurwitzQ


theorem solution {q : ℍ[ℚ]} (hq : q ∈ hurwitzIntegersQ) :
    (⟨(q.re : ℝ), (q.imI : ℝ), (q.imJ : ℝ), (q.imK : ℝ)⟩ : ℍ[ℝ]) ∈ hurwitzIntegers := by
  rcases hq with ⟨a, b, c, d, hqa, hqi, hqj, hqk⟩ | ⟨a, b, c, d, hqa, hqi, hqj, hqk⟩
  · refine .inl ⟨a, b, c, d, ?_, ?_, ?_, ?_⟩ <;>
      simp only [hqa, hqi, hqj, hqk] <;>
      push_cast <;> ring
  · refine .inr ⟨a, b, c, d, ?_, ?_, ?_, ?_⟩ <;>
      simp only [hqa, hqi, hqj, hqk] <;>
      push_cast <;> ring


