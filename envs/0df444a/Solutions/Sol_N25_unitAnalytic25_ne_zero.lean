-- Prove2me | solution 1 for N25.unitAnalytic25_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:49:30.539128+00:00
-- url     : https://prove2.me/submissions/38c69218-b0f4-4a83-ba0e-83d975987053

import Mathlib
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_N25_etaAnalytic25_ne_zero

set_option autoImplicit false

namespace N25

/-- All five unpowered analytic ratios are nonzero on the upper half-plane. -/
theorem _root_.solution (i : Fin 5) (τ : UpperHalfPlane) :
    unitAnalytic25 i τ ≠ 0 := by
  have bounds : ∀ j : Fin 5,
      0 < (unitResidues25 j).1 ∧ (unitResidues25 j).1 < 25 ∧
      0 < (unitResidues25 j).2 ∧ (unitResidues25 j).2 < 25 := by
    intro j
    fin_cases j <;> norm_num [unitResidues25]
  have hp : ∀ j : Fin 5, etaAnalytic25 (unitResidues25 j).1 τ *
      etaAnalytic25 (unitResidues25 j).2 τ ≠ 0 := by
    intro j
    exact mul_ne_zero (etaAnalytic25_ne_zero _ (bounds j).1 (bounds j).2.1 τ)
      (etaAnalytic25_ne_zero _ (bounds j).2.2.1 (bounds j).2.2.2 τ)
  exact div_ne_zero (hp i) (hp (i + 1))

end N25
