-- Prove2me | solution 1 for Kyprianou.Ch05.karamataGammaReference
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:48:43.3088+00:00
-- url     : https://prove2.me/submissions/d2b8eb9b-7f5e-4c48-a5bc-db9270357b33

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Theorems.Thm_Kyprianou_Ch05_karamataGammaLaplacePositive
import Theorems.Thm_Kyprianou_Ch05_karamataGammaCumulativePositive
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Select the Dirac reference at index zero and the power density otherwise. -/
theorem solution (rho : Real) (hrho : 0 ≤ rho) :
    ∃ R : Measure Real, R (Iio 0) = 0 ∧ R {1} = 0 ∧
      (R (Icc 0 1)).toReal = 1 / Real.Gamma (1+rho) ∧
      ∀ t : Real, 0 < t → positiveLaplace R t = ENNReal.ofReal (t^(-rho)) := by
  rcases eq_or_lt_of_le hrho with h | h
  · subst rho
    refine ⟨Measure.dirac 0, ?_, ?_, ?_, ?_⟩
    · rw [Measure.dirac_apply' _ measurableSet_Iio]
      simp
    · rw [Measure.dirac_apply' _ (measurableSet_singleton _)]
      norm_num
    · rw [Measure.dirac_apply' _ measurableSet_Icc]
      norm_num [Real.Gamma_one]
    · intro t ht
      simp [positiveLaplace,lintegral_dirac']
  · let R := (volume.restrict (Ioi (0 : Real))).withDensity
        (fun z : Real => ENNReal.ofReal (z^(rho-1)/Real.Gamma rho))
    refine ⟨R,?_,?_,karamataGammaCumulativePositive rho h,
      fun t ht => karamataGammaLaplacePositive rho t h ht⟩
    · dsimp [R]
      rw [withDensity_apply _ measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
      have he : Iio (0 : Real) ∩ Ioi 0 = ∅ := by
        ext z
        constructor
        · intro hz
          exact False.elim (lt_asymm (mem_Iio.mp hz.1) (mem_Ioi.mp hz.2))
        · intro hz
          exact False.elim hz
      simp [he]
    · dsimp [R]
      rw [withDensity_apply _ (measurableSet_singleton _)]
      simp
