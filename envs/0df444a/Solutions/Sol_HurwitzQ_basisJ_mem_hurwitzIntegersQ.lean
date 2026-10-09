-- Prove2me | solution 1 for HurwitzQ.basisJ_mem_hurwitzIntegersQ
-- status  : ACCEPTED   (prove)
-- author  : @jawneeboy
-- created : 2026-09-18T18:10:05.651232+00:00
-- url     : https://prove2.me/submissions/bc4b8f98-1ed6-4bd3-995c-daa1afabcca4

import Definitions.Def_HurwitzQ_hurwitzIntegersQ
import Definitions.Def_HurwitzQ_omega
import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.QuaternionBasis
import Mathlib.Tactic.Ring

/-!
# The standard generators lie in the Hurwitz integers

The three quaternion units `i, j, k` (Mathlib's `QuaternionAlgebra.Basis.self ℚ`) and the
half-integral generator `ω = (1 + i + j + k) / 2` are Hurwitz integers. These are the extra
membership facts beyond `Subring.zero_mem`, `one_mem'`, `add_mem`, `neg_mem`, `mul_mem`,
which hold for every subring; together they exhibit the generating set of
`hurwitzIntegersQ_eq_closure`.
-/

open Quaternion QuaternionAlgebra

open HurwitzQ




theorem solution : ((Basis.self ℚ).j : ℍ[ℚ]) ∈ hurwitzIntegersQ :=
  .inl ⟨0, 0, 1, 0, by simp, by simp, by simp, by simp⟩






