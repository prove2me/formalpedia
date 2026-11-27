-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45ActualPureJumpReconstructionV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-27T00:35:20.47579+00:00
-- url     : https://prove2.me/submissions/0da176bb-a0b0-4b32-861b-7736c35ea680
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch04_exercise45ActualSmallBandFullLimitV1
import Theorems.Thm_Kyprianou_Ch04_exercise45ActualPureJumpFixedTimeSubsequenceV1
import Theorems.Thm_Kyprianou_Ch04_exercise45RightContinuousDenseEqV1
import Theorems.Thm_Kyprianou_Ch04_exercise45PhysicalLargeRightV1
import Theorems.Thm_Kyprianou_Ch04_pathJumpMeasureZeroTimeV1
import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false

open Kyprianou.Ch04
theorem solution :
∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hLevy : ProbabilityTheory.IsLevyProcess X P)
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    [SigmaFinite triplet.levyMeasure]
    (hNoGaussian : triplet.gaussianVariance = 0)
    (hTriplet : ∀ (t : NNReal) (xi : Real),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : Real) : Complex) *
          Kyprianou.Ch01.levyTripleExponent triplet xi))
    (N : PoissonRandomMeasure.{0,0,0}
      P triplet.levyMeasure)
    (Xleft : NNReal -> Omega -> Real)
    (hLeft : ∀ᵐ omega : Omega ∂P, ∀ t : NNReal, 0 < t ->
      Tendsto (fun s : NNReal => X s omega)
        (nhdsWithin t (Set.Iio t)) (nhds (Xleft t omega)))
    (hLeftZero : ∀ᵐ w ∂P, Xleft 0 w = X 0 w)
    (hNLaw : ∀ᵐ omega : Omega ∂P,
      N.N omega = Kyprianou.Ch04.pathJumpMeasure X Xleft omega),
    let X2 : NNReal → Omega → ℝ := fun t w =>
      triplet.drift * (t : ℝ) +
        ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}, z.2 ∂(N.N w)
    let Y : ℝ → NNReal → Omega → ℝ := fun e t w =>
      X2 t w + (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | e < |x| ∧ |x| < 1},
        z.2 ∂(N.N w)) -
        (t : ℝ) * ∫ x in {x : ℝ | e < |x| ∧ |x| < 1}, x ∂triplet.levyMeasure
    ∀ᵐ w ∂P, ∀ t : NNReal,
      Tendsto (fun e : ℝ => Y e t w) (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (X t w)) := by
  intro Ω m P hP X hX triplet hSigma hGaussian hTriplet N L hL hL0 hN V Y
  have h0 : ∀ᵐ w ∂P, N.N w ({0} ×ˢ (univ : Set ℝ)) = 0 := by
    filter_upwards [hN] with w hw
    rw [hw]
    exact pathJumpMeasureZeroTimeV1 X L w
  obtain ⟨Z,hZ⟩ := exercise45ActualSmallBandFullLimitV1 P triplet.levyMeasure
    triplet.levyMeasure_isLevyMeasure N h0
  have hR := exercise45PhysicalLargeRightV1 P triplet.levyMeasure
    triplet.levyMeasure_isLevyMeasure N X L triplet.drift hN
  have hY : ∀ᵐ w ∂P, ∀ t, Tendsto (fun e => Y e t w)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (V t w + Z t w)) := by
    filter_upwards [hZ] with w hw
    intro t
    have hc : Tendsto (fun _ : ℝ => V t w)
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (V t w)) := tendsto_const_nhds
    simpa only [Y,sub_eq_add_neg,add_assoc] using hc.add (hw t).2
  have hfixed (t : NNReal) : ∀ᵐ w ∂P, X t w = V t w + Z t w := by
    obtain ⟨e,he,hel⟩ := exercise45ActualPureJumpFixedTimeSubsequenceV1
      P X hX triplet hGaussian hTriplet N L hL hL0 hN t
    filter_upwards [hY,hel] with w hw hv
    exact tendsto_nhds_unique hv ((hw t).comp he)
  obtain ⟨grid,hd⟩ := TopologicalSpace.exists_dense_seq NNReal
  filter_upwards [hY,hZ,hR,hX.cadlag_ae,ae_all_iff.mpr (fun k => hfixed (grid k))]
    with w hy hz hr hx he
  have hall := exercise45RightContinuousDenseEqV1 (fun t => X t w)
    (fun t => V t w + Z t w) grid hd (fun t => (hx t).1)
    (fun t => (hr t).add (hz t).1) he
  intro t
  rw [hall t]
  exact hy t
