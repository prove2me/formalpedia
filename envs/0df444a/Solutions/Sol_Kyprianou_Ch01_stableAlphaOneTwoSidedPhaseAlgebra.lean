-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneTwoSidedPhaseAlgebra
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T15:48:32.154446+00:00
-- url     : https://prove2.me/submissions/b9c5cd63-0cbe-4c57-95d7-7a88c9b6ba20

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Real Set Kyprianou.Ch01
set_option autoImplicit false

theorem solution (cpos cneg k xi : ℝ) :
    (cpos : ℂ) *
          ((((Real.pi * |xi| / 2 : ℝ) : ℂ) +
            Complex.I * (((xi * Real.log |xi| : ℝ) : ℂ)) -
            Complex.I * (((k * xi : ℝ) : ℂ)))) +
        (cneg : ℂ) *
          ((((Real.pi * |xi| / 2 : ℝ) : ℂ) -
            Complex.I * (((xi * Real.log |xi| : ℝ) : ℂ)) +
            Complex.I * (((k * xi : ℝ) : ℂ)))) = (((Real.pi * (cpos + cneg) * |xi| / 2 : ℝ) : ℂ) +
        Complex.I * (((((cpos - cneg) * xi * Real.log |xi| : ℝ)) : ℂ)) -
        Complex.I * (((((cpos - cneg) * k * xi : ℝ)) : ℂ))) := by
  push_cast
  ring
