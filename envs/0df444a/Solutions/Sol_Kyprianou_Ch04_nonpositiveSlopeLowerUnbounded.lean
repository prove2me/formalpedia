-- Prove2me | solution 1 for Kyprianou.Ch04.nonpositiveSlopeLowerUnbounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:47:16.621515+00:00
-- url     : https://prove2.me/submissions/dfec3e9a-8cd5-4078-bb94-b33610a17f2e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch03_exercise35LaplaceExponentRegularity
import Theorems.Thm_Kyprianou_Ch03_firstPassageTransform_maximalRootExistence
import Theorems.Thm_Kyprianou_Ch04_nonSingularInfimumTransform
import Theorems.Thm_Kyprianou_Ch04_lowerUnboundedFromInfimumZero
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- A vanishing nonnegative secant infimum forces lower-unbounded paths. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (hNotNegativeSubordinator : ¬ (∀ᵐ w : Ω ∂P, Antitone (fun t : NNReal => L.X t w)))
    (hm : max 0 (sInf ((fun theta : ℝ => L.ψ theta / theta) '' Ioi 0)) = 0) :
    P {w | BddBelow (range (fun t : NNReal => L.X t w))} = 0 := by
  let : IsProbabilityMeasure P := L.isProbability
  have hzero := (Kyprianou.Ch03.exercise35LaplaceExponentRegularity P F L).1
  obtain ⟨r,hr,hroot,_⟩ :=
    Kyprianou.Ch03.firstPassageTransform_maximalRootExistence P F L hNotNegativeSubordinator 1 (by norm_num)
  have hp : 0 < r := by
    apply lt_of_le_of_ne hr
    intro he
    rw [← he,hzero] at hroot
    norm_num at hroot
  have hn : L.ψ r ≠ 0 := by rw [hroot]; norm_num
  have hlim := Kyprianou.Ch04.nonSingularInfimumTransform P F L hNotNegativeSubordinator r hp hn
  rw [hm,zero_mul,zero_div] at hlim
  exact Kyprianou.Ch04.lowerUnboundedFromInfimumZero P F L r hp hlim
