-- Prove2me | solution 1 for Kyprianou.Ch04.bvSubcriticalSecantLower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:48:32.358182+00:00
-- url     : https://prove2.me/submissions/93fcae99-f3f4-4912-80e5-f852f7537c6b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_bvNormalizedExponentGapV1
import Theorems.Thm_Kyprianou_Ch04_normalizedDeficitMomentCharacterisationV1
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Finite jump mean bounds every positive exponent secant below. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) (hBV : L.BoundedVariation) (hd : 0 < L.drift)
    (hMtop : (∫⁻ y : ℝ, ENNReal.ofReal (-y) ∂L.ν) ≠ ⊤)
    (a : ℝ) (ha : 0 < a) :
    L.drift - (∫⁻ y : ℝ, ENNReal.ofReal (-y) ∂L.ν).toReal ≤ L.ψ a / a := by
  let M := ∫⁻ y : ℝ, ENNReal.ofReal (-y) ∂L.ν
  have hg := (Kyprianou.Ch04.normalizedDeficitMomentCharacterisationV1 L.ν M.toReal).mp
    (by rw [ENNReal.ofReal_toReal hMtop]) a ha
  rw [Kyprianou.Ch04.bvNormalizedExponentGapV1 P F L hBV hd a ha,
    ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg, div_le_iff₀ ha] at hg
  apply (le_div_iff₀ ha).2
  nlinarith
