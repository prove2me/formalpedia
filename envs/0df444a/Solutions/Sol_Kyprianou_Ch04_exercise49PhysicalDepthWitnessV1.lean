-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49PhysicalDepthWitnessV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:06:16.345871+00:00
-- url     : https://prove2.me/submissions/93c4f94c-4cc4-4e3e-80f6-fa5e8d77a54e

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise49AllPathCadlagVersionV1
import Theorems.Thm_Kyprianou_Ch04_exercise49AllPathDepthWitnessV1
import Definitions.Def_Kyprianou_Ch04_Exercise4_9CertificationV3
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false
/-- Transfer the measurable all-path witness by indistinguishability. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hLevy : ProbabilityTheory.IsLevyProcess X P)
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    (hTriplet : ∀ (t : NNReal) (theta : Real),
      charFun (P.map (X t)) theta =
        Complex.exp (((t : Real) : Complex) *
          Kyprianou.Ch01.levyTripleExponent triplet theta))
    (hBV : triplet.gaussianVariance = 0 ∧
      (∫⁻ y in Set.Ioo (-1 : Real) 1,
        ENNReal.ofReal |y| ∂triplet.levyMeasure) < ⊤)
    (drift : Real)
    (hDrift : drift = triplet.drift -
      ∫ y in Set.Ioo (-1 : Real) 1, y ∂triplet.levyMeasure)
    (hd : 0 < drift)
    (hNotSubordinator :
      ¬ (∀ᵐ omega : Omega ∂P, Monotone (fun t : NNReal => X t omega)))
    (hTendsInfinity : ∀ᵐ omega : Omega ∂P,
      Tendsto (fun t : NNReal => X t omega) atTop atTop) :
    let tau : Real -> Omega -> WithTop NNReal := fun initial omega =>
          sInf {v : WithTop NNReal |
            ∃ t : NNReal, v = ↑t ∧ 0 < t ∧
              initial + X t omega < 0}
        let rho : Real := (P {omega : Omega | tau 0 omega ≠ ⊤}).toReal
        0 < rho → rho < 1 →
        ∀ (finiteTime : Omega → NNReal),
          Measurable finiteTime →
          (∀ᵐ omega : Omega ∂P, tau 0 omega ≠ ⊤ →
            tau 0 omega = (finiteTime omega : WithTop NNReal)) →
          ∃ (D : Set Omega) (I V W : Omega → ℝ),
            MeasurableSet D ∧ Measurable I ∧ Measurable V ∧ Measurable W ∧
            (P D = P {omega : Omega | tau 0 omega ≠ ⊤}) ∧
            (∀ B : Set Real, MeasurableSet B →
              P (I ⁻¹' B ∩ D) = P {omega : Omega | tau 0 omega ≠ ⊤ ∧
                -(X (finiteTime omega) omega) ∈ B}) ∧
            (∀ x : Real, 0 ≤ x →
              P (V ⁻¹' Set.Iic x) = P {omega : Omega | tau x omega = ⊤}) ∧
            (∀ᵐ omega ∂P.restrict Dᶜ, V omega = 0) ∧
            (∀ᵐ omega ∂P.restrict D, V omega = I omega + W omega) ∧
            Measure.map (fun omega => (I omega, W omega)) (P.restrict D) =
              (Measure.map I (P.restrict D)).prod (Measure.map V P) := by
  dsimp only
  intro h0 h1 f hf he
  obtain ⟨Y, hY, hm, hc, hEq⟩ := Kyprianou.Ch04.exercise49AllPathCadlagVersionV1 P X hLevy
  have hInf : ∀ᵐ w ∂P, Tendsto (fun t : NNReal => Y t w) atTop atTop := by
    filter_upwards [hTendsInfinity, hEq] with w hi hw
    simpa only [hw] using hi
  have hfY : ∀ᵐ w ∂P,
      sInf {v : WithTop NNReal | ∃ t : NNReal,
        v = ↑t ∧ 0 < t ∧ 0 + Y t w < 0} ≠ ⊤ →
      sInf {v : WithTop NNReal | ∃ t : NNReal,
        v = ↑t ∧ 0 < t ∧ 0 + Y t w < 0} = (f w : WithTop NNReal) := by
    filter_upwards [he, hEq] with w hw h
    simpa only [h] using hw
  obtain ⟨D, I, V, W, hD, hI, hV, hW, hMass, hDef, hCDF, hZero, hSplit, hJoint⟩ :=
    Kyprianou.Ch04.exercise49AllPathDepthWitnessV1 P Y hY hm hc hInf f hf hfY
  refine ⟨D, I, V, W, hD, hI, hV, hW, ?_, ?_, ?_, hZero, hSplit, hJoint⟩
  · rw [hMass]
    apply measure_congr
    filter_upwards [hEq] with w hw
    change (sInf {v : WithTop NNReal | ∃ t : NNReal,
      v = ↑t ∧ 0 < t ∧ 0 + Y t w < 0} ≠ ⊤) =
      (sInf {v : WithTop NNReal | ∃ t : NNReal,
      v = ↑t ∧ 0 < t ∧ 0 + X t w < 0} ≠ ⊤)
    simp only [hw]
  · intro B hB
    rw [hDef B hB]
    apply measure_congr
    filter_upwards [hEq] with w hw
    change ((sInf {v : WithTop NNReal | ∃ t : NNReal,
      v = ↑t ∧ 0 < t ∧ 0 + Y t w < 0} ≠ ⊤) ∧ -(Y (f w) w) ∈ B) =
      ((sInf {v : WithTop NNReal | ∃ t : NNReal,
      v = ↑t ∧ 0 < t ∧ 0 + X t w < 0} ≠ ⊤) ∧ -(X (f w) w) ∈ B)
    simp only [hw]
  · intro x hx
    rw [hCDF x hx]
    apply measure_congr
    filter_upwards [hEq] with w hw
    change (sInf {v : WithTop NNReal | ∃ t : NNReal,
      v = ↑t ∧ 0 < t ∧ x + Y t w < 0} = ⊤) =
      (sInf {v : WithTop NNReal | ∃ t : NNReal,
      v = ↑t ∧ 0 < t ∧ x + X t w < 0} = ⊤)
    simp only [hw]
