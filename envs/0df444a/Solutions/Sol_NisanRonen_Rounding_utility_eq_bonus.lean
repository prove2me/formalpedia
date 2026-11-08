-- Prove2me | solution 1 for NisanRonen.Rounding.utility_eq_bonus
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:20:31.06437+00:00
-- url     : https://prove2.me/submissions/fae418b3-d9d2-4cad-b988-df0e8cb1e01c

import Mathlib
import Definitions.Def_NisanRonen_Rounding_utility

open NisanRonen.Rounding in
theorem solution {n k : ℕ} [NeZero n] (f : List (Fin n → ℕ) → List (Fin n)) (δ : ℝ)
    (s : Fin n → Strategy n k) (i : Fin n) :
    utility f δ s i =
      - roundedMakespan δ (allocOf f δ (fun l => (s l).decl))
          (corr i (allocOf f δ (fun l => (s l).decl)) (fun l => (s l).decl)
            (actualTimes f δ s)) := by
  simp only [utility]
  ring
