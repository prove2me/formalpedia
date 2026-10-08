-- Prove2me | solution 1 for MonotoneCompStatics.QSMChar.qsm_of_supermodularizable
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T03:48:04.61093+00:00
-- url     : https://prove2.me/submissions/3586ca0a-4a94-436b-8d18-67a9672af495

import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
import Definitions.Def_MonotoneCompStatics_Monotonicity_QuasiSupermodularOn

theorem solution {X : Type*} [Lattice X] (f : X → ℝ)
    (h : ℝ → ℝ) (hh : StrictMono h)
    (hsm : Supermodularity.Monotonicity.SupermodularOn (h ∘ f) Set.univ) :
    MonotoneCompStatics.Monotonicity.QuasiSupermodularOn f Set.univ := by
  intro x hx y hy
  have hs := hsm hx hy
  simp only [Function.comp_apply] at hs
  constructor
  · intro hle
    apply hh.le_iff_le.mp
    have := hh.monotone hle
    linarith
  · intro hlt
    apply hh.lt_iff_lt.mp
    have := hh hlt
    linarith

#print axioms solution
