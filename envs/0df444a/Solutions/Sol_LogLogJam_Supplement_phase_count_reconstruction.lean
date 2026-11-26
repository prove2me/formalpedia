-- Prove2me | solution 1 for LogLogJam.Supplement.phase_count_reconstruction
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T09:18:57.010466+00:00
-- url     : https://prove2.me/submissions/a7ee441f-f59a-46a3-9de6-185b334fbe97

import Mathlib
import Theorems.Thm_BosonicLearn_traceDist_triangle
import Theorems.Thm_LogLogJam_Supplement_radial_distance_le_parameter
import Theorems.Thm_LogLogJam_Supplement_squeezing_from_photon_mean
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P47

open MeasureTheory BosonicLearn
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ENNReal

open LogLogJam.Supplement

/-- The finite-sample composition step of §8.3.4: the phase estimator controls
the equal-squeezing comparison to the intermediate state, and a photon-number
mean estimate controls the remaining equal-angle comparison via Eq. (179).
The histograms may have any joint law. -/
theorem solution
    {X : Type} [MeasurableSpace X] (ν : Measure X)
    (ρ : State (Occupation (Fin 1))) (mid est : X → State (Occupation (Fin 1)))
    (μ : X → ℝ) {r a η : ℝ} {d₁ d₂ : ℝ≥0∞}
    (hr : 0 ≤ r) (ha : 0 ≤ a) (hη : 0 ≤ η) (hsmall : η ≤ 1 / 4) (hμ : ∀ x, 0 ≤ μ x)
    (phase : ν {x | ENNReal.ofReal a < traceDist ρ.coefficients (mid x).coefficients} ≤ d₁)
    (count : ν {x | η * Real.cosh r * Real.sinh r < |μ x - Real.sinh r ^ 2|} ≤ d₂)
    (sameAngle : ∀ x, traceDist (mid x).coefficients (est x).coefficients =
      ENNReal.ofReal (Real.sqrt (1 - 1 / Real.cosh (Real.arsinh (Real.sqrt (μ x)) - r)))) :
    ν {x | ENNReal.ofReal (a + 4 * η) < traceDist ρ.coefficients (est x).coefficients} ≤ d₁ + d₂ := by
  let A := {x | ENNReal.ofReal a < traceDist ρ.coefficients (mid x).coefficients}
  let B := {x | η * Real.cosh r * Real.sinh r < |μ x - Real.sinh r ^ 2|}
  have hsub : {x | ENNReal.ofReal (a + 4 * η) < traceDist ρ.coefficients (est x).coefficients} ⊆ A ∪ B := by
    intro x hx
    by_contra! h
    have h₁ : traceDist ρ.coefficients (mid x).coefficients ≤ ENNReal.ofReal a :=
      le_of_not_gt (fun bad => h (Or.inl bad))
    have h₂ : |μ x - Real.sinh r ^ 2| ≤ η * Real.cosh r * Real.sinh r :=
      le_of_not_gt (fun bad => h (Or.inr bad))
    have hrad := (radial_distance_le_parameter (Real.arsinh (Real.sqrt (μ x))) r).trans
      (squeezing_from_photon_mean hr (hμ x) hη hsmall h₂)
    have hbound := traceDist_triangle ρ.coefficients (mid x).coefficients (est x).coefficients
    rw [sameAngle x] at hbound
    exact (not_lt_of_ge ((hbound.trans (add_le_add h₁ (ENNReal.ofReal_le_ofReal hrad))).trans_eq
      (ENNReal.ofReal_add ha (by positivity)).symm)) hx
  exact (measure_mono hsub).trans ((measure_union_le A B).trans (add_le_add phase count))
