-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45BoundedPhysicalWitnessV2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-27T00:25:45.707205+00:00
-- url     : https://prove2.me/submissions/59c1ac91-5f5c-4723-af34-930f9ea8c974
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch04_exercise45PRMNoOriginVersionV2
import Theorems.Thm_Kyprianou_Ch04_pathJumpMeasureZeroTimeV1
import Theorems.Thm_Kyprianou_Ch04_exercise45CutoffSupplyV1
import Theorems.Thm_Kyprianou_Ch04_exercise45ActualPureJumpReconstructionV1
import Theorems.Thm_Kyprianou_Ch04_exercise45BoundedWitnessFromSuppliedCutoffsV1
import Theorems.Thm_Kyprianou_Ch04_exercise45UCPIndistinguishableCongrV1
import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false
open Kyprianou.Ch04

theorem solution :
  ∀ {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P] (F :
  Filtration NNReal (inferInstance : MeasurableSpace Omega)) (X : NNReal -> Omega -> Real) (hLevy
  : ProbabilityTheory.IsLevyProcess X P) (triplet : ProbabilityTheory.LevyKhintchineTriple)
  [SigmaFinite triplet.levyMeasure] (hNoGaussian : triplet.gaussianVariance = 0) (hTriplet : ∀ (t
  : NNReal) (xi : Real), charFun (P.map (X t)) xi = Complex.exp (((t : Real) : Complex) *
  Kyprianou.Ch01.levyTripleExponent triplet xi)) (hFiltration :
  Kyprianou.Ch03.IsCompletedNaturalFiltration P X F) (N : PoissonRandomMeasure.{0,0,0} P
  triplet.levyMeasure) (Xleft : NNReal -> Omega -> Real) (hLeft : ∀ᵐ omega : Omega ∂P, ∀ t :
  NNReal, 0 < t -> Tendsto (fun s : NNReal => X s omega) (nhdsWithin t (Set.Iio t)) (nhds (Xleft t
  omega))) (hLeftZero : ∀ᵐ w ∂P, Xleft 0 w = X 0 w) (hNLaw : ∀ᵐ omega : Omega ∂P, N.N omega =
  Kyprianou.Ch04.pathJumpMeasure X Xleft omega) (f fTime fSpace fSpace2 : Real -> Real -> Real)
  (hTime : ∀ s x : Real, fTime s x = deriv (fun u : Real => f u x) s) (hSpace : ∀ s x : Real,
  fSpace s x = deriv (fun u : Real => f s u) x) (hSpace2 : ∀ s x : Real, fSpace2 s x = deriv (fun
  u : Real => fSpace s u) x) (hSmoothTime : ∀ x : Real, ContDiff Real 1 (fun s => f s x))
  (hSmoothSpace : ∀ s : Real, ContDiff Real 2 (fun x => f s x)) (hJoint : ContinuousOn (fun z :
  Real × Real => f z.1 z.2) (Set.Ici (0 : Real) ×ˢ Set.univ) ∧ ContinuousOn (fun z : Real × Real
  => fTime z.1 z.2) (Set.Ici (0 : Real) ×ˢ Set.univ) ∧ ContinuousOn (fun z : Real × Real => fSpace
  z.1 z.2) (Set.Ici (0 : Real) ×ˢ Set.univ) ∧ ContinuousOn (fun z : Real × Real => fSpace2 z.1
  z.2) (Set.Ici (0 : Real) ×ˢ Set.univ)) (X2 : NNReal -> Omega -> Real) (hX2Representation : ∀ t
  omega, X2 t omega = triplet.drift * (t : Real) + ∫ z in Set.prod (Set.Icc (0 : Real) (t : Real))
  {x : Real | 1 ≤ |x|}, z.2 ∂(N.N omega)) (K : Real) (hK : 0 < K) (hBound : ∀ s x : Real, 0 ≤ s →
  |f s x| ≤ K ∧ |fTime s x| ≤ K ∧ |fSpace s x| ≤ K ∧ |fSpace2 s x| ≤ K),
    let D : NNReal → Omega → Real := fun t omega =>
        triplet.drift * (∫ s in Set.Icc (0 : Real) (t : Real), fSpace s (Xleft s.toNNReal omega)) +
        ∫ z in Set.Icc (0 : Real) (t : Real) ×ˢ {x : Real | 1 ≤ |x|},
          z.2 * fSpace z.1 (Xleft z.1.toNNReal omega) ∂(N.N omega)
    let R : NNReal → Omega → Real := fun t omega =>
      f (t : Real) (X t omega) - (
              f 0 (X 0 omega) +
              (∫ s in Set.Icc (0 : Real) (t : Real),
                fTime s (X (Real.toNNReal s) omega) ∂volume) +
              (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real)) Set.univ,
                (f z.1 (Xleft (Real.toNNReal z.1) omega + z.2) -
                 f z.1 (Xleft (Real.toNNReal z.1) omega) -
                 z.2 * fSpace z.1 (Xleft (Real.toNNReal z.1) omega))
                ∂(N.N omega)))
    ∃ M : NNReal → Omega → Real,
      Martingale M F P ∧
      (∀ᵐ w ∂P, ∀ t, ContinuousWithinAt (fun u => M u w) (Ici t) t) ∧
      IsStochasticIntegralInProbabilityV2 P X
        (fun t w => fSpace (t : ℝ) (Xleft t w)) (fun t w => D t w + M t w) ∧
      (∀ᵐ w ∂P, ∀ t, R t w = D t w + M t w)
 := by
  intro Ω m P hP F X hLevy triplet hSigma hNoGaussian hTriplet hFiltration N
    Xleft hLeft hLeftZero hNLaw f ft fx fxx hTime hSpace hSpace2 hST hSS hJoint
    X2 hX2 K hK hBound D R
  have h0 : ∀ᵐ w ∂P, N.N w (({0} : Set ℝ) ×ˢ (univ : Set ℝ)) = 0 :=
    by
      filter_upwards [hNLaw] with w hw
      rw [hw]
      exact pathJumpMeasureZeroTimeV1 X Xleft w
  obtain ⟨Q,hQ,hQ0⟩ := exercise45PRMNoOriginVersionV2 P triplet.levyMeasure N h0
  have hQLaw : ∀ᵐ w ∂P, Q.N w = pathJumpMeasure X Xleft w := by
    filter_upwards [hQ,hNLaw] with w hq hn
    exact hq.trans hn
  let B := {x : ℝ | 1 ≤ |x|}
  let A (e : ℝ) := {x : ℝ | e < |x| ∧ |x| < 1}
  let V (t : NNReal) (w : Ω) := triplet.drift * (t : ℝ) +
    ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ B, z.2 ∂(Q.N w)
  let Y (e : ℝ) (t : NNReal) (w : Ω) := V t w +
    (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ A e, z.2 ∂(Q.N w)) -
    (t : ℝ) * ∫ x in A e, x ∂triplet.levyMeasure
  obtain ⟨L,hInit,hLeftY⟩ := exercise45CutoffSupplyV1 P X Xleft hLevy
    triplet Q hQLaw hQ0
  let J (e : ℝ) (t : NNReal) (w : Ω) :=
    (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ A e, z.2 * fx z.1 (L e z.1.toNNReal w) ∂(Q.N w)) -
      ∫ s in Icc (0 : ℝ) (t : ℝ),
        (∫ x in A e, x * fx s (L e s.toNNReal w) ∂triplet.levyMeasure) ∂volume
  have hConv : ∀ᵐ w ∂P, ∀ t : NNReal,
      Tendsto (fun e : ℝ => Y e t w) (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (X t w)) :=
    exercise45ActualPureJumpReconstructionV1 P X hLevy triplet hNoGaussian hTriplet
      Q Xleft hLeft hLeftZero hQLaw
  obtain ⟨M,hMart,hRC,hU,hIto⟩ := exercise45BoundedWitnessFromSuppliedCutoffsV1
    P F X hLevy triplet hNoGaussian hTriplet hFiltration Q Xleft hLeft hQLaw
    f ft fx fxx hTime hSpace hSpace2 hST hSS hJoint K hK hBound Y L V
    hInit hLeftY (fun _ _ => rfl) (fun _ _ _ _ _ => rfl) J (fun _ _ _ _ _ => rfl) hConv
  refine ⟨M,hMart,hRC,?_,?_⟩
  · refine exercise45UCPIndistinguishableCongrV1 P X _ _ X _ _ ?_ hU
    filter_upwards [hQ] with w hw
    intro t
    exact ⟨rfl,rfl,by dsimp only [D]; rw [hw]⟩
  · filter_upwards [hQ,hIto] with w hq hi
    intro t
    have h := hi t
    rw [hq] at h
    exact h
