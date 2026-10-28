-- Prove2me | solution 1 for HScattered.Delsarte.theorem_2_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T08:31:44.703883+00:00
-- url     : https://prove2.me/submissions/e3f23b25-17f1-4914-8e27-ac500c5473e7

import Mathlib
import Definitions.Def_HScattered_Delsarte_IsHScattered
import Definitions.Def_HScattered_Construction_DefinesSubgeometry
import Theorems.Thm_HScattered_Bound_theorem_2_3

open HScattered.Delsarte


/-- Theorem 2.3 (arXiv:1906.10590v2, p. 4): an h-scattered `𝔽_q`-subspace `U` of the
r-dimensional `𝔽_{qⁿ}`-space `V` either has dimension `r`, defines a subgeometry of
`PG(V, 𝔽_{qⁿ})` and is (r − 1)-scattered, or satisfies `dim_{𝔽_q} U ≤ rn/(h + 1)`
(stated as `(h + 1) · dim_{𝔽_q} U ≤ r · n`). -/
theorem solution {F K V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    [Fintype F] [Fintype K] [FiniteDimensional K V]
    (h : ℕ) (U : Submodule F V) (hU : IsHScattered F K h U) :
    (Module.finrank F U = Module.finrank K V ∧ HScattered.Construction.DefinesSubgeometry F K U ∧
        IsHScattered F K (Module.finrank K V - 1) U) ∨
      (h + 1) * Module.finrank F U ≤ Module.finrank K V * Module.finrank F K :=
  HScattered.Bound.theorem_2_3 h U hU
