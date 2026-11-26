-- Prove2me | solution 1 for Kyprianou.Ch04.subcriticalPathsBoundedBelowAE
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:47:22.553549+00:00
-- url     : https://prove2.me/submissions/3edd46c4-7344-44aa-826b-4e43f9ea1bc4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_totalIdleTrafficMaximalRootV1
import Theorems.Thm_Kyprianou_Ch04_bvSubcriticalSecantSlope
import Theorems.Thm_Kyprianou_Ch04_limitingDrawdown_positiveMeanClassification
import Theorems.Thm_Kyprianou_Ch03_exercise35LaplaceExponentRegularity
import Theorems.Thm_Kyprianou_Ch04_nonpositiveSecantSlopeIff
import Theorems.Thm_Kyprianou_Ch04_infimumLimitSupport
open MeasureTheory AvramDividend.Classical Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Positive subcritical traffic implies almost-sure boundedness below of the process. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) (hBV : L.BoundedVariation) (hd : 0 < L.drift)
    (hr0 : 0 < (∫⁻ y : ℝ, ENNReal.ofReal (-y) ∂L.ν) / ENNReal.ofReal L.drift)
    (hr1 : (∫⁻ y : ℝ, ENNReal.ofReal (-y) ∂L.ν) / ENNReal.ofReal L.drift < 1) :
    ∀ᵐ z ∂P, BddBelow (range (fun t : NNReal => L.X t z)) := by
  let : IsProbabilityMeasure P := L.isProbability
  let m := max 0 (sInf ((fun a : ℝ => L.ψ a/a) '' Ioi 0))
  obtain ⟨hm,hpos⟩ := Kyprianou.Ch04.bvSubcriticalSecantSlope P F L hBV hd hr0 hr1
  have hmpos : 0 < m := by rw [show m = _ from hm]; exact hpos
  obtain ⟨hz,_,hc,_,_⟩ := Kyprianou.Ch03.exercise35LaplaceExponentRegularity P F L
  have hn := (Kyprianou.Ch04.totalIdleTrafficMaximalRootV1 P F L hBV hd).1
  have hmean : ¬ (∀ e : ℝ, 0 < e → ∃ a : ℝ, 0 < a ∧ L.ψ a < e*a) :=
    fun h => hmpos.ne' ((Kyprianou.Ch04.nonpositiveSecantSlopeIff L.ψ hc hz).mp h)
  have hp := Kyprianou.Ch04.limitingDrawdown_positiveMeanClassification P F L hn hmean
  let B : Set Ω := {z | BddBelow (range (fun t : NNReal => L.X t z))}
  have hB : MeasurableSet B := (Kyprianou.Ch04.infimumLimitSupport P F L 1 zero_lt_one).1
  change (P B).toReal = 1 at hp
  have he := ENNReal.ofReal_toReal (measure_ne_top P B)
  rw [hp,ENNReal.ofReal_one] at he
  rw [ae_iff]
  change P Bᶜ = 0
  rw [measure_compl hB (measure_ne_top P B),← he,measure_univ,tsub_self]
