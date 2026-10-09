-- Prove2me | solution 1 for HurwitzQ.omega_mem_hurwitzIntegersQ
-- status  : ACCEPTED   (prove)
-- author  : @jawneeboy
-- created : 2026-09-18T18:10:17.912007+00:00
-- url     : https://prove2.me/submissions/69571735-e379-4244-ac83-bee2e24dcc9a

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








theorem solution : omega ∈ hurwitzIntegersQ :=
  .inr ⟨0, 0, 0, 0, by simp [omega], by simp [omega], by simp [omega], by simp [omega]⟩


