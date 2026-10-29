-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.foldl_edges_scalar
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:55:48.82458+00:00
-- url     : https://prove2.me/submissions/730816dc-1fdf-45af-9c6f-eef81ea14670

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.R6.Bit

theorem solution {Wr : Type*} [DecidableEq Wr] {R : Type*} [CommRing R] {m : ℕ}
    (es : List (Wr × Edge m)) (v : Wr → R) :
    (es.map fun p => Instr.edge (R := R) p.1 p.2).foldl scalarStepH v = v := by
  induction es generalizing v with
  | nil => simp
  | cons p es ih =>
    simpa [scalarStepH] using ih v
