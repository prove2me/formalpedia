-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49UnnormalisedRenewalLawV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:52:53.32692+00:00
-- url     : https://prove2.me/submissions/c9a9b785-e27d-495e-8acd-e4ee0b8a9076

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise49PhysicalDepthWitnessV1
import Theorems.Thm_Kyprianou_Ch04_exercise49DepthMeasureAssemblyV1
import Definitions.Def_Kyprianou_Ch04_Exercise4_9CertificationV3
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false
/-- Assemble the physical witness into its defective measure identity. -/
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
          ∃ nu mu : Measure Real,
            nu Set.univ = ENNReal.ofReal rho ∧
            IsProbabilityMeasure mu ∧
            (∀ B : Set Real, MeasurableSet B →
              nu B = P {omega : Omega | tau 0 omega ≠ ⊤ ∧
                -(X (finiteTime omega) omega) ∈ B}) ∧
            (∀ x : Real, 0 ≤ x →
              (P {omega : Omega | tau x omega = ⊤}).toReal =
                (mu (Set.Iic x)).toReal) ∧
            mu = ENNReal.ofReal (1 - rho) • Measure.dirac 0 + mu.conv nu := by
  dsimp only
  intro h0 h1 f hf he
  obtain ⟨D, I, V, W, hD, hI, hV, hW, hMass, hDef, hCDF, hZero, hSplit, hJoint⟩ :=
    Kyprianou.Ch04.exercise49PhysicalDepthWitnessV1 P X hLevy triplet
      hTriplet hBV drift hDrift hd hNotSubordinator hTendsInfinity h0 h1 f hf he
  let nu := Measure.map I (P.restrict D)
  let mu := Measure.map V P
  have hMu : IsProbabilityMeasure mu := Measure.isProbabilityMeasure_map hV.aemeasurable
  have hnu : nu univ = P D := by
    rw [Measure.map_apply hI MeasurableSet.univ]
    simp
  have htotal := measure_add_measure_compl (μ := P) hD
  have hr : ENNReal.ofReal (P D).toReal = P D :=
    ENNReal.ofReal_toReal (measure_ne_top P D)
  have hc : ENNReal.ofReal (1 - (P D).toReal) = P Dᶜ := by
    have hs : (P D).toReal + (P Dᶜ).toReal = 1 := by
      rw [← ENNReal.toReal_add (measure_ne_top P _) (measure_ne_top P _), htotal]
      simp
    rw [show 1 - (P D).toReal = (P Dᶜ).toReal by linarith,
      ENNReal.ofReal_toReal (measure_ne_top P _)]
  refine ⟨nu, mu, ?_, hMu, ?_, ?_, ?_⟩
  · rw [hnu, ← hMass, hr]
  · intro B hB
    rw [Measure.map_apply hI hB, Measure.restrict_apply (hI hB), hDef B hB]
  · intro x hx
    rw [Measure.map_apply hV measurableSet_Iic, hCDF x hx]
  · rw [← hMass, hc]
    exact Kyprianou.Ch04.exercise49DepthMeasureAssemblyV1 P D hD I V W
      hI hV hW hZero hSplit hJoint
