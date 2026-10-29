-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.LabGates_edges
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:55:49.494987+00:00
-- url     : https://prove2.me/submissions/cac25bcb-0f47-42a0-aec2-bb860789bb89

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192

open IntMul.Kappa.R6.Bit

theorem solution {Wr : Type*} [Fintype Wr] [DecidableEq Wr] {R : Type*} [CommRing R]
    {m N : ℕ} (es : List (Wr × Edge m)) (L : Wr → FMat m N) :
    LabGates N (es.map fun p => Instr.edge (R := R) p.1 p.2) L := by
  induction es generalizing L with
  | nil => simp [LabGates]
  | cons p es ih =>
    refine ⟨trivial, ?_⟩
    simpa [labStepH] using ih (labStepH (R := R) N L (Instr.edge p.1 p.2))
