-- Prove2me | solution 1 for MangasarianFJ.GenFJ.region_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:38:04.394061+00:00
-- url     : https://prove2.me/submissions/cd4ec564-1307-486d-be66-bf0d7fcedcd1

import Mathlib
import Definitions.Def_MangasarianFJ_GenFJ_Setting

set_option autoImplicit false
open MangasarianFJ.GenFJ

theorem solution {n m : ℕ} (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : ∀ i, Continuous (g i)) (xbar : EuclideanSpace ℝ (Fin n)) :
    IsOpen (region g xbar) := by
  have : region g xbar = ⋂ i ∈ ({i : Fin m | i ∉ activeSet g xbar} : Set (Fin m)),
      {x | g i x < 0} := by
    ext x
    simp [region]
  rw [this]
  exact (Set.toFinite _).isOpen_biInter (fun i _ => isOpen_lt (hg i) continuous_const)

