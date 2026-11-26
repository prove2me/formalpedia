-- Prove2me | solution 1 for Kyprianou.Ch04.bvSecantLowerBoundsJumpMean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:46:16.876136+00:00
-- url     : https://prove2.me/submissions/2608564e-102f-4b2d-9a50-043f7463118a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_bvNormalizedExponentGapV1
import Theorems.Thm_Kyprianou_Ch04_normalizedDeficitMomentCharacterisationV1
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- A lower bound on exponent secants bounds the jump mean. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) (hBV : L.BoundedVariation) (hd : 0 < L.drift)
    (m : ℝ) (hm : ∀ a : ℝ, 0 < a → m ≤ L.ψ a / a) :
    (∫⁻ y : ℝ, ENNReal.ofReal (-y) ∂L.ν) ≤ ENNReal.ofReal (L.drift-m) := by
  apply (Kyprianou.Ch04.normalizedDeficitMomentCharacterisationV1 L.ν (L.drift-m)).mpr
  intro a ha
  rw [Kyprianou.Ch04.bvNormalizedExponentGapV1 P F L hBV hd a ha]
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_iff₀ ha).2
  have h' := (le_div_iff₀ ha).1 (hm a ha)
  nlinarith
