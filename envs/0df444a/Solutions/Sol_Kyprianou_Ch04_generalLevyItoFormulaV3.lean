-- Prove2me | solution 1 for Kyprianou.Ch04.generalLevyItoFormulaV3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:15:52.435526+00:00
-- url     : https://prove2.me/submissions/064c22fe-57f1-43d4-8c87-796045e214d1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_ito43_time_grid_ucp
import Theorems.Thm_Kyprianou_Ch04_ito43_spatial_remainder_ucpV2
import Theorems.Thm_Kyprianou_Ch04_ito43_ucp_transfer
import Theorems.Thm_Kyprianou_Ch04_ito43_residual_error
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
theorem solution {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P] (X : NNReal -> Omega -> Real)
    (hLevy : ProbabilityTheory.IsLevyProcess X P)
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    (hTriplet : forall (t : NNReal) (xi : Real), charFun (P.map (X t)) xi =
        Complex.exp (((t : Real) : Complex) * Kyprianou.Ch01.levyTripleExponent triplet xi))
    (Xleft : NNReal -> Omega -> Real)
    (hLeftZero : ∀ᵐ omega ∂P, Xleft 0 omega = X 0 omega)
    (hLeft : ∀ᵐ omega : Omega ∂P, forall t : NNReal, 0 < t ->
        Tendsto (fun s : NNReal => X s omega) (nhdsWithin t (Set.Iio t)) (nhds (Xleft t omega)))
    (f : Real × Real -> Real) (hfJointC1 : ContDiffOn Real 1 f
      (Set.prod (Set.Ici (0 : Real)) Set.univ)) (hfSpaceC2 : forall s : NNReal,
      ContDiff Real 2 (fun x : Real => f ((s : Real), x))) (hfSpaceSecondContinuous : ContinuousOn
        (fun z : Real × Real => iteratedDeriv 2 (fun x : Real => f (z.1, x)) z.2)
        (Set.prod (Set.Ici (0 : Real)) Set.univ)) :
    ∃ (stochasticIntegral : NNReal -> Omega -> Real), IsStochasticIntegralInProbabilityV2 P X
        (fun s omega => fderiv Real f ((s : Real), Xleft s omega) (0, 1)) stochasticIntegral ∧
      (∀ᵐ omega : Omega ∂P, forall t : NNReal, f ((t : Real), X t omega) = f (0, X 0 omega) +
        (∫ s in Set.Icc (0 : Real) (t : Real),
          fderiv Real f ((s : Real), X (Real.toNNReal s) omega) (1, 0) ∂volume) +
        stochasticIntegral t omega + ((triplet.gaussianVariance : Real) / 2) *
          (∫ s in Set.Icc (0 : Real) (t : Real), iteratedDeriv 2
              (fun x : Real => f ((s : Real), x)) (X (Real.toNNReal s) omega) ∂volume) +
        (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real)) (Set.univ : Set Real),
          (f (z.1, Xleft (Real.toNNReal z.1) omega + z.2) -
           f (z.1, Xleft (Real.toNNReal z.1) omega) - z.2 * fderiv Real f
             (z.1, Xleft (Real.toNNReal z.1) omega) (0, 1)) ∂(pathJumpMeasure X Xleft omega))):= by
  let A : NNReal → Omega → Real := fun t omega => ∫ s in Set.Icc (0 : Real) (t : Real),
          fderiv Real f ((s : Real), X (Real.toNNReal s) omega) (1, 0) ∂volume
  let Q : NNReal → Omega → Real := fun t omega => ((triplet.gaussianVariance : Real) / 2) *
          (∫ s in Set.Icc (0 : Real) (t : Real),
            iteratedDeriv 2 (fun x : Real => f ((s : Real), x))
              (X (Real.toNNReal s) omega) ∂volume)
  let J : NNReal → Omega → Real := fun t omega => (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real))
            (Set.univ : Set Real),
          (f (z.1, Xleft (Real.toNNReal z.1) omega + z.2) -
           f (z.1, Xleft (Real.toNNReal z.1) omega) -
           z.2 * fderiv Real f
             (z.1, Xleft (Real.toNNReal z.1) omega) (0, 1))
          ∂(pathJumpMeasure X Xleft omega))
  let I : NNReal → Omega → Real := fun t omega =>
    f ((t : Real), X t omega) - f (0, X 0 omega) -
      A t omega - Q t omega - J t omega
  refine ⟨I, ?_, ?_⟩
  · intro T epsilon he
    let E : ℕ → NNReal → Omega → Real := fun n t omega =>
      let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
      let v : ℕ → NNReal := fun k => min t (u k)
      A t omega - (∑ k ∈ Finset.range n,
          (f ((v (k+1) : Real), X (v (k+1)) omega) -
          f ((v k : Real), X (v (k+1)) omega)))
    let G : ℕ → NNReal → Omega → Real := fun n t omega =>
      let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
      let v : ℕ → NNReal := fun k => min t (u k)
      Q t omega + J t omega - (∑ k ∈ Finset.range n,
          (f ((v k : Real), X (v (k+1)) omega) -
          f ((v k : Real), X (v k) omega) -
          fderiv Real f ((u k : Real), Xleft (u k) omega) (0, 1) *
            (X (v (k+1)) omega - X (v k) omega)))
    have hE : ∀ e : ℝ, 0 < e → Tendsto
        (fun n => (P {w | ∃ t ≤ T, e ≤ |E n t w|}).toReal) atTop (nhds 0) :=
      Kyprianou.Ch04.ito43_time_grid_ucp P X hLevy f hfJointC1 T
    have hG : ∀ e : ℝ, 0 < e → Tendsto
        (fun n => (P {w | ∃ t ≤ T, e ≤ |G n t w|}).toReal) atTop (nhds 0) :=
      Kyprianou.Ch04.ito43_spatial_remainder_ucpV2 P X hLevy triplet hTriplet Xleft
        hLeftZero hLeft f hfJointC1 hfSpaceC2 hfSpaceSecondContinuous T
    apply Kyprianou.Ch04.ito43_ucp_transfer P E G _ T hE hG _ epsilon he
    intro n hn t ht omega
    have H := Kyprianou.Ch04.ito43_residual_error
      (fun s => X s omega)
      (fun s => fderiv Real f ((s : Real), Xleft s omega) (0, 1))
      f T t ht n hn (A t omega) (Q t omega + J t omega)
    dsimp [I,E,G]; dsimp at H
    linarith
  · filter_upwards [] with omega
    intro t
    change f ((t : Real), X t omega) =
      f (0, X 0 omega) + A t omega + I t omega + Q t omega + J t omega
    dsimp [I]
    ring
