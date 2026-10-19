-- Prove2me | solution 1 for OAI.PiExponent.MatrixTranslationBounds.tail_coeff_formula
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:47:40.756005+00:00
-- url     : https://prove2.me/submissions/c244e628-b553-4a15-8f58-7456714b25a8

import Mathlib
import Mathlib.RingTheory.PowerSeries.Trunc
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData

open OAI.PiExponent.RowTranslation
theorem solution {R : Type*} [CommRing R] (T n : ℕ) (f : PowerSeries R) :
    PowerSeries.coeff n (OAI.PiExponent.RowTranslation.tail T f) =
      if n < T then 0 else -PowerSeries.coeff n f := by
  unfold OAI.PiExponent.RowTranslation.tail
  rw [map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  split_ifs <;> simp
