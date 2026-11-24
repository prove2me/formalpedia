-- Prove2me | solution 1 for HodgeComputer.Formal.QuadraticCovers.residue_mapRatFunc
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T03:34:51.555377+00:00
-- url     : https://prove2.me/submissions/8f515fc1-8f0c-4e5f-8099-7a6babd57443

import Definitions.Def_HodgeComputerFormal_CoverResidues
import Mathlib.Tactic

set_option autoImplicit false
open CrossedRationalResidue QuadraticCovers

theorem solution
    {K L : Type*} [Field K] [Field L] (f : K →+* L) (a : K) (g : RatFunc K) :
    CrossedRationalResidue.residue (f a) (QuadraticCovers.mapRatFunc f g) =
      f (CrossedRationalResidue.residue a g) := by
  obtain ⟨r, terms, hr, rfl⟩ := exists_regular_add_poleSum a g
  rw [map_add, map_add, map_add, hr.residue_eq_zero, (RegularAt.mapRatFunc f hr).residue_eq_zero,
    zero_add, zero_add]
  induction terms with
  | nil => simp [poleSum]
  | cons t ts ih =>
    rcases t with ⟨c, n⟩
    simp only [poleSum, map_add, map_mul, map_inv₀, map_pow, mapRatFunc_C, mapRatFunc_uniformizer]
    rw [residue_term, residue_term, ih]
    by_cases hn : n = 0 <;> simp [hn]
