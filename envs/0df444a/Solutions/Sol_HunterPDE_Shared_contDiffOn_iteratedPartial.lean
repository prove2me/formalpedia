-- Prove2me | solution 1 for HunterPDE.Shared.contDiffOn_iteratedPartial
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T20:11:46.10238+00:00
-- url     : https://prove2.me/submissions/aa3c67e3-fd23-4efc-a28b-572d2516a44e

import Definitions.Def_HunterPDE_Shared_PartialDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Positivity

open scoped ContDiff
open HunterPDE.Shared
set_option autoImplicit false

theorem solution {n : ℕ} {s : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hs : IsOpen s) (hu : ContDiffOn ℝ ∞ u s)
    (l : List (Fin n)) : ContDiffOn ℝ ∞ (iteratedPartial u l) s := by
  induction l with
  | nil => exact hu
  | cons i l ih =>
    exact ((contDiffOn_infty_iff_fderiv_of_isOpen hs).mp ih).2.clm_apply contDiffOn_const
