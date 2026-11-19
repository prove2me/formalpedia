-- Prove2me | solution 1 for Kyprianou.Ch03.exercise35LaplaceExponentRegularity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T13:12:43.561203+00:00
-- url     : https://prove2.me/submissions/9047dc9b-61a9-4e23-81d0-d88f0054a57f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch03_exponentRegularity_zeroAtOrigin
import Theorems.Thm_Kyprianou_Ch03_exponentRegularity_smoothPositive
import Theorems.Thm_Kyprianou_Ch03_exponentRegularity_convexNonnegative
import Theorems.Thm_Kyprianou_Ch03_exponentRegularity_strictConvexNontrivial
import Theorems.Thm_Kyprianou_Ch03_exponentRegularity_infiniteLimitNonSubordinator
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch03


theorem solution
{Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F) :
    L.ψ 0 = 0 ∧
    ContDiffOn ℝ (⊤ : WithTop ℕ∞) L.ψ (Set.Ioi 0) ∧
    ConvexOn ℝ (Set.Ici 0) L.ψ ∧
    ((0 < L.σ ∨ L.ν ≠ 0) →
      StrictConvexOn ℝ (Set.Ioi 0) L.ψ) ∧
    ((¬ (∀ᵐ omega : Omega ∂P,
        Antitone (fun t : NNReal => L.X t omega))) →
      Tendsto L.ψ atTop atTop) := by
  exact ⟨
    Kyprianou.Ch03.exponentRegularity_zeroAtOrigin P F L,
    Kyprianou.Ch03.exponentRegularity_smoothPositive P F L,
    Kyprianou.Ch03.exponentRegularity_convexNonnegative P F L,
    Kyprianou.Ch03.exponentRegularity_strictConvexNontrivial P F L,
    Kyprianou.Ch03.exponentRegularity_infiniteLimitNonSubordinator P F L
  ⟩

