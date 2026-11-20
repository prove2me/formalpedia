-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneTwoSidedIntegralValue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T15:56:32.63818+00:00
-- url     : https://prove2.me/submissions/3dbffc6a-ee00-4f66-97e7-ad489c6b4ce1

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLogPhaseAllReal
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneTwoSidedPhaseAlgebra
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Real Set Kyprianou.Ch01
set_option autoImplicit false

theorem solution (cpos cneg : ℝ) :
    ∃ k : ℝ, ∀ xi : ℝ,
      let F : ℝ → ℂ := (fun z : ℝ =>
      ∫ r in Set.Ioi (0 : ℝ),
        ((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
            Complex.I * (((z * r : ℝ) : ℂ)) *
              (if r < 1 then (1 : ℂ) else 0)) /
          ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) ∂volume)
      (cpos : ℂ) * F xi + (cneg : ℂ) * F (-xi) = (((Real.pi * (cpos + cneg) * |xi| / 2 : ℝ) : ℂ) +
        Complex.I * ((((cpos - cneg) * xi * Real.log |xi| : ℝ) : ℂ)) -
        Complex.I * ((((cpos - cneg) * k * xi : ℝ) : ℂ))) := by
  obtain ⟨k, hk⟩ := Kyprianou.Ch01.stableAlphaOneLogPhaseAllReal
  refine ⟨k, ?_⟩
  intro xi F
  have hp : F xi = (((Real.pi * |xi| / 2 : ℝ) : ℂ) +
          Complex.I * (((xi * Real.log |xi| : ℝ) : ℂ)) -
          Complex.I * (((k * xi : ℝ) : ℂ))) := by
    simpa only [F] using hk xi
  have hn : F (-xi) = (((Real.pi * |xi| / 2 : ℝ) : ℂ) -
          Complex.I * (((xi * Real.log |xi| : ℝ) : ℂ)) +
          Complex.I * (((k * xi : ℝ) : ℂ))) := by
    have h := hk (-xi)
    change F (-xi) = _ at h
    convert h using 1 <;> simp only [abs_neg] <;> push_cast <;> ring
  calc
    (cpos : ℂ) * F xi + (cneg : ℂ) * F (-xi) =
      (cpos : ℂ) * (((Real.pi * |xi| / 2 : ℝ) : ℂ) +
          Complex.I * (((xi * Real.log |xi| : ℝ) : ℂ)) -
          Complex.I * (((k * xi : ℝ) : ℂ))) + (cneg : ℂ) * (((Real.pi * |xi| / 2 : ℝ) : ℂ) -
          Complex.I * (((xi * Real.log |xi| : ℝ) : ℂ)) +
          Complex.I * (((k * xi : ℝ) : ℂ))) := by rw [hp, hn]
    _ = (((Real.pi * (cpos + cneg) * |xi| / 2 : ℝ) : ℂ) +
        Complex.I * ((((cpos - cneg) * xi * Real.log |xi| : ℝ) : ℂ)) -
        Complex.I * ((((cpos - cneg) * k * xi : ℝ) : ℂ))) := Kyprianou.Ch01.stableAlphaOneTwoSidedPhaseAlgebra cpos cneg k xi
