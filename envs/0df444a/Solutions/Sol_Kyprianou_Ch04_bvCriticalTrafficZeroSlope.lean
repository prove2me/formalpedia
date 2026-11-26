-- Prove2me | solution 1 for Kyprianou.Ch04.bvCriticalTrafficZeroSlope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:16:25.995424+00:00
-- url     : https://prove2.me/submissions/a474fb6e-7af8-4dc7-9053-d479922b1a25

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_bvNormalizedExponentGapV1
import Theorems.Thm_Kyprianou_Ch04_normalizedDeficitMomentCharacterisationV1
import Theorems.Thm_Kyprianou_Ch03_exercise35LaplaceExponentRegularity
import Theorems.Thm_Kyprianou_Ch04_nonpositiveSecantSlopeIff
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Critical or greater traffic forces the nonnegative secant infimum to vanish. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) (hBV : L.BoundedVariation) (hd : 0 < L.drift)
    (htraffic : 1 ≤ (∫⁻ y : ℝ, ENNReal.ofReal (-y) ∂L.ν) / ENNReal.ofReal L.drift) :
    max 0 (sInf ((fun a : ℝ => L.ψ a / a) '' Ioi 0)) = 0 := by
  let : IsProbabilityMeasure P := L.isProbability
  let M := ∫⁻ y : ℝ, ENNReal.ofReal (-y) ∂L.ν
  let D := ENNReal.ofReal L.drift
  have hDM : D ≤ M := by
    change 1 ≤ M / D at htraffic
    rwa [ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl ENNReal.ofReal_ne_top),
      one_mul] at htraffic
  obtain ⟨hz,_,hc,_,_⟩ := Kyprianou.Ch03.exercise35LaplaceExponentRegularity P F L
  apply (Kyprianou.Ch04.nonpositiveSecantSlopeIff L.ψ hc hz).mp
  intro ε he
  by_contra! hn
  let e := min ε (L.drift / 2)
  have he0 : 0 < e := lt_min he (by positivity)
  have heD : 0 ≤ L.drift - e := by dsimp [e]; linarith [min_le_right ε (L.drift/2)]
  have hM : M ≤ ENNReal.ofReal (L.drift - e) := by
    apply (Kyprianou.Ch04.normalizedDeficitMomentCharacterisationV1 L.ν (L.drift-e)).mpr
    intro a ha
    rw [Kyprianou.Ch04.bvNormalizedExponentGapV1 P F L hBV hd a ha,
      ENNReal.ofReal_le_ofReal_iff heD, div_le_iff₀ ha]
    have hb := hn a ha
    have hle := mul_le_mul_of_nonneg_right (min_le_left ε (L.drift/2)) ha.le
    dsimp [e]
    linarith
  have hlt : ENNReal.ofReal (L.drift-e) < D :=
    (ENNReal.ofReal_lt_ofReal_iff hd).mpr (by linarith)
  exact (not_lt_of_ge (hDM.trans hM)) hlt
