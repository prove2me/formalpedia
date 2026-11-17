-- Prove2me | solution 1 for N25.unitAnalytic25_mdifferentiable
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:49:29.841208+00:00
-- url     : https://prove2.me/submissions/6870cae9-5942-4ff7-afc2-745d5d70aeba

import Mathlib
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_N25_etaAnalytic25_mdifferentiable
import Theorems.Thm_N25_etaAnalytic25_ne_zero

set_option autoImplicit false

open scoped Manifold

namespace N25

theorem _root_.solution (i : Fin 5) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (unitAnalytic25 i) := by
  have hb : ∀ j : Fin 5,
      (0 < (unitResidues25 j).1 ∧ (unitResidues25 j).1 < 25) ∧
      (0 < (unitResidues25 j).2 ∧ (unitResidues25 j).2 < 25) := by decide
  exact ((etaAnalytic25_mdifferentiable (unitResidues25 i).1).mul
      (etaAnalytic25_mdifferentiable (unitResidues25 i).2)).div
    ((etaAnalytic25_mdifferentiable (unitResidues25 (i + 1)).1).mul
      (etaAnalytic25_mdifferentiable (unitResidues25 (i + 1)).2))
    (fun τ => mul_ne_zero
      (etaAnalytic25_ne_zero _ (hb (i + 1)).1.1 (hb (i + 1)).1.2 τ)
      (etaAnalytic25_ne_zero _ (hb (i + 1)).2.1 (hb (i + 1)).2.2 τ))

end N25
