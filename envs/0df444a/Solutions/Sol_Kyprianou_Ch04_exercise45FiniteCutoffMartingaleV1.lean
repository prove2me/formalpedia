-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45FiniteCutoffMartingaleV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T09:49:46.030016+00:00
-- url     : https://prove2.me/submissions/79f2ef99-5fd8-49c7-9fa6-6716544e4a44

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_actualPoissonPastMeasurableV1
import Theorems.Thm_Kyprianou_Ch04_actualPoissonFutureIndependenceV1
import Theorems.Thm_Kyprianou_Ch04_actualCutoffAdaptedV1
import Theorems.Thm_Kyprianou_Ch04_adaptedAELeftPredictableVersionV1
import Theorems.Thm_Kyprianou_Ch04_actualCutoffMartingaleSquareFromVersionV1
import Theorems.Thm_Kyprianou_Ch04_exercise45ActualCutoffRightV1
open MeasureTheory Set Topology
open MeasureTheory ProbabilityTheory Filter ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Construct the actual physical cutoff martingale and its right-continuous square-integrable version. -/
theorem solution : ∀ {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega)
    [IsProbabilityMeasure P] (F : Filtration NNReal (inferInstance : MeasurableSpace Omega)) (X :
    NNReal -> Omega -> Real) (hLevy : ProbabilityTheory.IsLevyProcess X P) (triplet :
    ProbabilityTheory.LevyKhintchineTriple) [SigmaFinite triplet.levyMeasure] (hNoGaussian :
    triplet.gaussianVariance = 0) (hTriplet : ∀ (t : NNReal) (xi : Real), charFun (P.map (X t)) xi
    = Complex.exp (((t : Real) : Complex) * Kyprianou.Ch01.levyTripleExponent triplet xi))
    (hFiltration : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F) (N :
    PoissonRandomMeasure.{0,0,0} P triplet.levyMeasure) (Xleft : NNReal -> Omega -> Real) (hLeft :
    ∀ᵐ omega : Omega ∂P, ∀ t : NNReal, 0 < t -> Tendsto (fun s : NNReal => X s omega) (nhdsWithin
    t (Set.Iio t)) (nhds (Xleft t omega))) (hNLaw : ∀ᵐ omega : Omega ∂P, N.N omega =
    Kyprianou.Ch04.pathJumpMeasure X Xleft omega) (f fTime fSpace fSpace2 : Real -> Real -> Real)
    (hTime : ∀ s x : Real, fTime s x = deriv (fun u : Real => f u x) s) (hSpace : ∀ s x : Real,
    fSpace s x = deriv (fun u : Real => f s u) x) (hSpace2 : ∀ s x : Real, fSpace2 s x = deriv
    (fun u : Real => fSpace s u) x) (hSmoothTime : ∀ x : Real, ContDiff Real 1 (fun s => f s x))
    (hSmoothSpace : ∀ s : Real, ContDiff Real 2 (fun x => f s x)) (hJoint : ContinuousOn (fun z :
    Real × Real => f z.1 z.2) (Set.Ici (0 : Real) ×ˢ Set.univ) ∧ ContinuousOn (fun z : Real × Real
    => fTime z.1 z.2) (Set.Ici (0 : Real) ×ˢ Set.univ) ∧ ContinuousOn (fun z : Real × Real =>
    fSpace z.1 z.2) (Set.Ici (0 : Real) ×ˢ Set.univ) ∧ ContinuousOn (fun z : Real × Real =>
    fSpace2 z.1 z.2) (Set.Ici (0 : Real) ×ˢ Set.univ)) (K : Real) (hK : 0 < K) (hBound : ∀ s x :
    Real, 0 ≤ s -> |f s x| ≤ K ∧ |fTime s x| ≤ K ∧ |fSpace s x| ≤ K ∧ |fSpace2 s x| ≤ K) (Xeps :
    Real -> NNReal -> Omega -> Real) (XepsLeft : Real -> NNReal -> Omega -> Real) (X2 : NNReal ->
    Omega -> Real) (hXepsInitial : ∀ epsilon omega, 0 < epsilon -> epsilon < 1 -> Xeps epsilon 0
    omega = X 0 omega) (hXepsLeft : ∀ epsilon : Real, 0 < epsilon -> epsilon < 1 -> ∀ᵐ omega :
    Omega ∂P, ∀ t : NNReal, 0 < t -> Tendsto (fun s : NNReal => Xeps epsilon s omega) (nhdsWithin
    t (Set.Iio t)) (nhds (XepsLeft epsilon t omega))) (hX2Representation : ∀ t omega, X2 t omega =
    triplet.drift * (t : Real) + ∫ z in Set.prod (Set.Icc (0 : Real) (t : Real)) {x : Real | 1 ≤
    |x|}, z.2 ∂(N.N omega)) (hXepsRepresentation : ∀ (epsilon : Real), 0 < epsilon -> epsilon < 1
    -> ∀ t omega, Xeps epsilon t omega = X2 t omega + (∫ z in Set.prod (Set.Icc (0 : Real) (t :
    Real)) {x : Real | epsilon < |x| ∧ |x| < 1}, z.2 ∂(N.N omega)) - (t : Real) * (∫ x in {x :
    Real | epsilon < |x| ∧ |x| < 1}, x ∂triplet.levyMeasure)), ∀ epsilon : Real, 0 < epsilon ->
    epsilon < 1 -> let M : NNReal → Omega → Real := fun t omega => (∫ z in Set.prod (Set.Icc (0 :
    Real) (t : Real)) {x : Real | epsilon < |x| ∧ |x| < 1}, z.2 * fSpace z.1 (XepsLeft epsilon
    (Real.toNNReal z.1) omega) ∂(N.N omega)) - (∫ s in Set.Icc (0 : Real) (t : Real), (∫ x in {x :
    Real | epsilon < |x| ∧ |x| < 1}, x * fSpace s (XepsLeft epsilon (Real.toNNReal s) omega)
    ∂triplet.levyMeasure) ∂volume); MeasureTheory.Martingale M F P ∧ (∀ t : NNReal, Integrable
    (fun omega : Omega => (M t omega)^2) P) ∧ (∀ᵐ omega : Omega ∂P, ∀ t : NNReal, Tendsto (fun s :
    NNReal => M s omega) (nhdsWithin t (Set.Ioi t)) (nhds (M t omega))) := by
  intro Ω m P hP F X hLevy triplet hSigma hNoGaussian hTriplet hFiltration N
    Xleft hLeft hNLaw f fTime fSpace fSpace2 hTime hSpace hSpace2 hSmoothTime
    hSmoothSpace hJoint K hK hBound Xeps XepsLeft X2 hXepsInitial hXepsLeft
    hX2Representation hXepsRepresentation e he he1
  let ν := triplet.levyMeasure
  have hPast := Kyprianou.Ch04.actualPoissonPastMeasurableV1 P ν F X Xleft
    hLevy hFiltration N hLeft hNLaw
  have hFuture := Kyprianou.Ch04.actualPoissonFutureIndependenceV1 P ν F X Xleft
    hLevy hFiltration N hLeft hNLaw
  let M : ℝ → NNReal → Ω → ℝ := fun a t w =>
    (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | a < |x| ∧ |x| < 1},
      z.2 * fSpace z.1 (XepsLeft a z.1.toNNReal w) ∂(N.N w)) -
    ∫ s in Icc (0 : ℝ) (t : ℝ), ∫ x in {x : ℝ | a < |x| ∧ |x| < 1},
      x * fSpace s (XepsLeft a s.toNNReal w) ∂ν ∂volume
  have hAll (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
      Martingale (M a) F P ∧ ∀ t, Integrable (fun w => (M a t w)^2) P := by
    have hA := Kyprianou.Ch04.actualCutoffAdaptedV1 P ν F N hPast triplet.drift
      a (Xeps a) X2 hX2Representation (hXepsRepresentation a ha ha1)
    obtain ⟨V,hV,hEq⟩ := Kyprianou.Ch04.adaptedAELeftPredictableVersionV1
      P X F hFiltration (Xeps a) (XepsLeft a) hA (hXepsLeft a ha ha1)
    have hfin : ν {x : ℝ | a < |x| ∧ |x| < 1} < ⊤ :=
      (measure_mono (show {x : ℝ | a < |x| ∧ |x| < 1} ⊆ {x : ℝ | a ≤ |x|}
        from fun x hx => hx.1.le)).trans_lt
        (triplet.levyMeasure_isLevyMeasure.measure_setOf_abs_ge_lt_top ha)
    exact Kyprianou.Ch04.actualCutoffMartingaleSquareFromVersionV1
      P ν X F hFiltration N hFuture hPast a K hK.le hfin fSpace hJoint.2.2.1
      (fun s x hs => (hBound s x hs).2.2.1) (XepsLeft a) V hV hEq (M a)
      (fun _ _ => rfl)
  have hr := Kyprianou.Ch04.exercise45ActualCutoffRightV1 P F X hLevy triplet
    hNoGaussian hTriplet hFiltration N Xleft hLeft hNLaw f fTime fSpace fSpace2
    hTime hSpace hSpace2 hSmoothTime hSmoothSpace hJoint K hK hBound Xeps
    XepsLeft X2 hXepsInitial hXepsLeft hX2Representation hXepsRepresentation
    1 zero_lt_one M (fun a ha ha1 => ⟨fun _ _ => rfl,(hAll a ha ha1).1⟩) e he he1
  exact ⟨(hAll e he he1).1,(hAll e he he1).2,hr⟩
