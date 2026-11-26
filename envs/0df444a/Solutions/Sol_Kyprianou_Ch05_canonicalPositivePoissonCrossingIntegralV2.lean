-- Prove2me | solution 1 for Kyprianou.Ch05.canonicalPositivePoissonCrossingIntegralV2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:17:40.989433+00:00
-- url     : https://prove2.me/submissions/e518c43c-02c0-4b11-a532-5c1ecfb7ffcb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_pointFamilyNonnegativeTimeKLSBridgeV1
import Theorems.Thm_Kyprianou_Ch05_pointFamilyNonanticipatingFiltrationV1
import Theorems.Thm_Kyprianou_Ch05_canonicalPositivePoissonCrossingWitnessV2
import Theorems.Thm_Kyprianou_Ch04_jointlyPredictableENNJumpCompensation
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set Complex Topology Kyprianou.Ch05
open scoped NNReal ENNReal Topology Classical
set_option autoImplicit false
theorem solution
    {Lambda : Type} [MeasurableSpace Lambda]
    (Q : Measure Lambda) [IsProbabilityMeasure Q]
    (Pi : Measure ℝ) [SigmaFinite Pi]
    (K : ℕ → Lambda → ℕ) (Z : ℕ → ℕ → Lambda → ℝ × ℝ)
    (hd : IsPoissonPointFamily K Z ((volume : Measure ℝ).prod Pi) Q)
    (eta d : ℝ) (heta : 0 ≤ eta) (hdrift : 0 ≤ d)
    (hs : Pi (Iic (0 : ℝ)) = 0)
    (hint : Integrable (fun z : ℝ => min (1 : ℝ) |z|) Pi)
    (x : ℝ) (hx : 0 < x) (A B : Set ℝ) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAp : A ⊆ Ioi (0 : ℝ)) (hBp : B ⊆ Icc (0 : ℝ) x)
    (H : (NNReal → ℝ) → ENNReal) (hHmeas : Measurable H)
    (hH : ∀ f : NNReal → ℝ, Monotone f → f 0 = 0 →
        (∀ t, ContinuousWithinAt f (Ici t) t) →
        (∀ t, 0 < t → ∃ l : ℝ, Tendsto f (nhdsWithin t (Iio t)) (nhds l)) →
        H f = ∑' t : NNReal, if 0 < t ∧ f t > x ∧
          Function.leftLim f t ∈ Icc (0 : ℝ) x ∧
          f t - x ∈ A ∧ x - Function.leftLim f t ∈ B then
          ENNReal.ofReal (Real.exp (-eta*(t : ℝ))) else 0) :
    let X := fun (t : NNReal) (w : Lambda) =>
      d * (t : ℝ) + (∫⁻ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ Ioi (0 : ℝ),
        ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)).toReal
    (∫⁻ f, H f ∂(Q.map (fun w t => X t w))) =
      ∫⁻ t in Ici (0 : ℝ), ENNReal.ofReal (Real.exp (-eta*t)) *
      (∫⁻ v, (fun v : ℝ => if v ∈ Icc (0 : ℝ) x then
          ∫⁻ z in Ioi (x-v), if z-(x-v) ∈ A ∧ x-v ∈ B then (1 : ENNReal) else 0 ∂Pi
        else 0) v ∂(Q.map (X (Real.toNNReal t)))) ∂volume := by
  dsimp only
  obtain ⟨N,hN⟩ := Kyprianou.Ch05.pointFamilyNonnegativeTimeKLSBridgeV1 Q Pi K Z hd
  obtain ⟨F,hFuture,hF⟩ := Kyprianou.Ch05.pointFamilyNonanticipatingFiltrationV1
    Q Pi K Z hd N hN
  obtain ⟨psi,hPsi,hL,hR⟩ := Kyprianou.Ch05.canonicalPositivePoissonCrossingWitnessV2
    Q Pi K Z hd eta d heta hdrift hs hint x hx A B hA hB hAp hBp H hHmeas hH N hN F hF
  have he (n : ℕ) := Kyprianou.Ch04.jointlyPredictableENNJumpCompensation
    Q Pi F N hFuture psi hPsi (n : NNReal)
  have hEq : (fun n : ℕ => ∫⁻ w, ∫⁻ z in Icc (0 : ℝ) (n : ℝ) ×ˢ univ,
        psi z.1 z.2 w ∂(N.N w) ∂Q) =
      (fun n : ℕ => ∫⁻ w, ∫⁻ t in Icc (0 : ℝ) (n : ℝ),
        ∫⁻ z, psi t z w ∂Pi ∂volume ∂Q) := by
    funext n
    have hh := Kyprianou.Ch04.jointlyPredictableENNJumpCompensation
      Q Pi F N hFuture psi hPsi (Real.toNNReal (n : ℝ))
    rw [Real.coe_toNNReal (n : ℝ) (Nat.cast_nonneg n)] at hh
    exact hh
  rw [hEq] at hL
  exact tendsto_nhds_unique hL hR
