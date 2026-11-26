-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41ZeroVisitsLocallyFiniteV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T09:39:05.272685+00:00
-- url     : https://prove2.me/submissions/9d402f10-c5a0-49d6-aec4-a962c18f819a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_exercise41PositiveSlopeWindowV1
import Theorems.Thm_Kyprianou_Ch04_exercise41BlockZeroFiniteV5
import Theorems.Thm_Kyprianou_Ch04_exercise41BlockCoverV5
open MeasureTheory AvramDividend.Classical Filter Kyprianou.Ch04
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Local finiteness from the positive-slope window, block estimates and a
countable intersection of full-measure events. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)
    (hd : 0 < L.drift) :
    ∀ᵐ omega : Omega ∂P, ∀ t : NNReal,
      Set.Finite {s : NNReal | 0 < s ∧ s ≤ t ∧ L.X s omega = 0} := by
  obtain ⟨δ, hδ, hp⟩ := exercise41PositiveSlopeWindowV1 P F L hBV hd
  have hb : ∀ k : ℕ, ∀ᵐ ω ∂P,
      Set.Finite {s : NNReal | (k : NNReal) * δ ≤ s ∧
        s < (k : NNReal) * δ + δ ∧ L.X s ω = 0} :=
    fun k => exercise41BlockZeroFiniteV5 P F L ((k : NNReal) * δ) δ hδ hd hp
  filter_upwards [ae_all_iff.mpr hb] with ω hω
  exact exercise41BlockCoverV5 (fun s => L.X s ω) δ hδ hω
