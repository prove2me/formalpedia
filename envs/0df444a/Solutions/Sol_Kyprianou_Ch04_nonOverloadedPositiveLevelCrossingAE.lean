-- Prove2me | solution 1 for Kyprianou.Ch04.nonOverloadedPositiveLevelCrossingAE
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:46:30.490797+00:00
-- url     : https://prove2.me/submissions/4b204d9d-8e04-4bb4-97ec-80d28aed3da3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_Kyprianou_Ch04_totalIdleTrafficMaximalRootV1
import Theorems.Thm_Kyprianou_Ch03_firstPassageZero_maximalRootExistence
import Theorems.Thm_Kyprianou_Ch03_firstPassageZero_consequence2
import Theorems.Thm_Kyprianou_Ch03_firstPassage_firstHittingIoi_isRightContStoppingTime
open MeasureTheory AvramDividend.Classical Filter Set Kyprianou.Ch03
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Under subcritical traffic every fixed positive level is eventually crossed. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) (hBV : L.BoundedVariation) (hd : 0 < L.drift)
    (hr : (∫⁻ y : ℝ, ENNReal.ofReal (-y) ∂L.ν) / ENNReal.ofReal L.drift ≤ 1)
    (x : ℝ) (hx : 0 < x) :
    ∀ᵐ z ∂P, ∃ t : NNReal, x < L.X t z := by
  letI : IsProbabilityMeasure P := L.isProbability
  have hroot := Kyprianou.Ch04.totalIdleTrafficMaximalRootV1 P F L hBV hd
  obtain ⟨phi,hphi⟩ := firstPassageZero_maximalRootExistence P F L hroot.1
  have hzero := (hroot.2 phi hphi.1 hphi.2.1 hphi.2.2).2 hr
  let T := firstHittingTime L.X (Ioi x)
  have hmass : (P {z | T z != ⊤}).toReal = 1 :=
    (firstPassageZero_consequence2 P F L hroot.1 phi hphi x hx).2 hzero
  have hmeas : Measurable T :=
    by
    have hs := firstPassage_firstHittingIoi_isRightContStoppingTime P F L x hx
    exact hs.measurable.mono hs.measurableSpace_le le_rfl
  have hE : MeasurableSet {z | T z != ⊤} := by
    convert (hmeas (measurableSet_singleton (⊤ : WithTop NNReal))).compl using 1
    ext z
    simp
  have hmass' : P {z | T z != ⊤} = 1 := by
    have h := ENNReal.ofReal_toReal (measure_ne_top P {z | T z != ⊤})
    rw [hmass, ENNReal.ofReal_one] at h
    exact h.symm
  have hae : ∀ᵐ z ∂P, T z != ⊤ := by
    rw [ae_iff]
    change P ({z | T z != ⊤}ᶜ) = 0
    rw [measure_compl hE (measure_ne_top _ _),hmass',measure_univ,tsub_self]
  filter_upwards [hae] with z hz
  by_contra h
  push_neg at h
  have hempty : {t : NNReal | 0 < t ∧ L.X t z ∈ Ioi x} = ∅ := by
    ext t
    simp [not_lt.mpr (h t)]
  have ht : T z = ⊤ := by
    unfold T firstHittingTime
    rw [hempty]
    simp only [image_empty,sInf_empty]
  simp [ht] at hz
