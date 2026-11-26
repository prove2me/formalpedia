-- Prove2me | solution 1 for Kyprianou.Ch04.stationaryWorkload_nonStationaryCriticalAndAbove
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:19:03.191835+00:00
-- url     : https://prove2.me/submissions/4c5757b7-fb5c-420e-a005-bb74ba648079

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_totalIdleTrafficMaximalRootV1
import Theorems.Thm_Kyprianou_Ch04_bvCriticalTrafficZeroSlope
import Theorems.Thm_Kyprianou_Ch04_limitingDrawdown_LaplaceTransform
import Theorems.Thm_Kyprianou_Ch04_fixedHorizonSignedExtremaMeasurable
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc
import Theorems.Thm_Kyprianou_Ch04_stationaryLawObstructedByVanishingDrawdown
open MeasureTheory AvramDividend.Classical Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Critical and greater traffic admit no stationary probability workload law. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)
    (hd : 0 < L.drift) :
    let rho : ENNReal :=
      (∫⁻ y : Real, ENNReal.ofReal (-y) ∂L.ν) /
        ENNReal.ofReal L.drift
    let eta : Measure Real :=
      ((volume : Measure Real).restrict (Set.Ioi 0)).withDensity
        (fun x : Real =>
          L.ν (Set.Iio (-x)) /
            (ENNReal.ofReal L.drift * rho))
    let convPow : Nat → Measure Real :=
      Nat.rec (Measure.dirac (0 : Real))
        (fun _ mu => mu.conv eta)
    (1 ≤ rho →
      ¬ ∃ mu : Measure Real,
        IsProbabilityMeasure mu ∧
        mu (Set.Ici (0 : Real)) = 1 ∧
        (∀ (t : NNReal) (f : BoundedContinuousFunction Real Real),
          (∫ w in Set.Ici (0 : Real),
            (∫ omega,
              f (max w
                (sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t)) -
                L.X t omega) ∂P) ∂mu) =
          ∫ w, f w ∂mu)) := by
  intro rho eta convPow hrho
  let : IsProbabilityMeasure P := L.isProbability
  let S (t : NNReal) (z : Omega) := sSup ((fun s : NNReal => L.X s z) '' Iic t)
  let D (t : NNReal) (z : Omega) := S t z - L.X t z
  let W (t : NNReal) (w : ℝ) (z : Omega) := max w (S t z) - L.X t z
  have hn := (Kyprianou.Ch04.totalIdleTrafficMaximalRootV1 P F L hBV hd).1
  have hm := Kyprianou.Ch04.bvCriticalTrafficZeroSlope P F L hBV hd hrho
  have hlim := Kyprianou.Ch04.limitingDrawdown_LaplaceTransform P F L hn 1 zero_lt_one
  simp only [hm,zero_mul,zero_div,neg_mul,one_mul] at hlim
  apply Kyprianou.Ch04.stationaryLawObstructedByVanishingDrawdown P D W
  · intro t
    have h := (Kyprianou.Ch04.fixedHorizonSignedExtremaMeasurable P F L t).1.neg
    change Measurable (fun z : Omega => -(L.X t z - S t z)) at h
    simpa only [neg_sub,D] using h
  · intro t z
    apply sub_nonneg.mpr
    have h := levyPath_bddAbove_Icc L z t
    change L.X t z ≤ sSup ((fun s : NNReal => L.X s z) '' Iic t)
    have hset : Icc (0 : NNReal) t = Iic t := by ext x; simp
    rw [hset] at h
    exact le_csSup h ⟨t,by simp,rfl⟩
  · intro t w z hw
    exact sub_le_sub_right (le_max_right w (S t z)) _
  · exact hlim
