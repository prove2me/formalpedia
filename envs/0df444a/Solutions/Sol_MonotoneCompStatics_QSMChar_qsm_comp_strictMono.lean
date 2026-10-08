-- Prove2me | solution 1 for MonotoneCompStatics.QSMChar.qsm_comp_strictMono
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T03:29:03.223589+00:00
-- url     : https://prove2.me/submissions/749c53b6-42dc-463e-8019-4b8ea0f4b7de

import Mathlib
import Definitions.Def_MonotoneCompStatics_Monotonicity_QuasiSupermodularOn

theorem solution {X : Type*} [Lattice X] (f : X → ℝ) (g : ℝ → ℝ)
    (hf : MonotoneCompStatics.Monotonicity.QuasiSupermodularOn f Set.univ) (hg : StrictMono g) :
    MonotoneCompStatics.Monotonicity.QuasiSupermodularOn (g ∘ f) Set.univ  := by
  intro x hx y hy
  obtain ⟨h₁, h₂⟩ := hf hx hy
  constructor
  · intro h
    exact hg.monotone (h₁ (hg.le_iff_le.mp h))
  · intro h
    exact hg (h₂ (hg.lt_iff_lt.mp h))

#print axioms solution
