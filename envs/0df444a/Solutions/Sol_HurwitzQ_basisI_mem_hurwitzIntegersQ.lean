-- Prove2me | solution 1 for HurwitzQ.basisI_mem_hurwitzIntegersQ
-- status  : ACCEPTED   (prove)
-- author  : @jawneeboy
-- created : 2026-09-18T18:10:04.886786+00:00
-- url     : https://prove2.me/submissions/1f8ad022-9d2d-4baf-9bac-620476e3e9d9

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


theorem solution : ((Basis.self ℚ).i : ℍ[ℚ]) ∈ hurwitzIntegersQ :=
  .inl ⟨0, 1, 0, 0, by simp, by simp, by simp, by simp⟩








