-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45JointCutoffProbabilityCauchyV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:08:29.983796+00:00
-- url     : https://prove2.me/submissions/652e7646-9cc2-49a3-a289-133dbafe2b9c

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
import Theorems.Thm_Kyprianou_Ch04_jointCutoffProbabilityFromSquareCauchyV1
import Theorems.Thm_Kyprianou_Ch04_exercise45StateCutoffSupCauchyV1
import Theorems.Thm_Kyprianou_Ch04_exercise45WeightedCutoffSupCauchyV1
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false
/-- Apply the joint probability estimate to the two physical compact square Cauchy families. -/
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
    Real | epsilon < |x| ∧ |x| < 1}, x ∂triplet.levyMeasure)) (Mε : Real -> NNReal -> Omega ->
    Real) (hMRepresentation : ∀ (epsilon : Real), 0 < epsilon -> epsilon < 1 -> ∀ t omega, Mε
    epsilon t omega = (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real)) {x : Real | epsilon < |x| ∧
    |x| < 1}, z.2 * fSpace z.1 (XepsLeft epsilon (Real.toNNReal z.1) omega) ∂(N.N omega)) - (∫ s
    in Set.Icc (0 : Real) (t : Real), (∫ x in {x : Real | epsilon < |x| ∧ |x| < 1}, x * fSpace s
    (XepsLeft epsilon (Real.toNNReal s) omega) ∂triplet.levyMeasure) ∂volume)), (∀ᵐ omega : Omega
    ∂P, ∀ t : NNReal, Tendsto (fun epsilon : Real => Xeps epsilon t omega) (nhdsWithin (0 : Real)
    (Set.Ioi 0)) (nhds (X t omega))) -> ∀ i : ℕ, ∃ J : ℕ, ∀ m n, J ≤ m → J ≤ n → P {w | ∃ t ≤ (i :
    NNReal), (2⁻¹ : ℝ)^i < dist (Xeps (1 / ((m : ℝ)+2)) t w,Mε (1 / ((m : ℝ)+2)) t w) (Xeps (1 /
    ((n : ℝ)+2)) t w,Mε (1 / ((n : ℝ)+2)) t w)} ≤ (2⁻¹ : ENNReal)^i := by
  intro Ω m P hP F X hLevy triplet hSigma hNoGaussian hTriplet hFiltration N
    Xleft hLeft hNLaw f fTime fSpace fSpace2 hTime hSpace hSpace2 hSmoothTime
    hSmoothSpace hJoint K hK hBound Xeps XepsLeft X2 hXepsInitial hXepsLeft
    hX2Representation hXepsRepresentation Mε hMRepresentation hConv
  apply Kyprianou.Ch04.jointCutoffProbabilityFromSquareCauchyV1 P Xeps Mε
  intro W hW
  rcases Set.mem_insert_iff.mp hW with h | h
  · subst W
    exact Kyprianou.Ch04.exercise45StateCutoffSupCauchyV1 P F X hLevy triplet
      hNoGaussian hTriplet hFiltration N Xleft hLeft hNLaw f fTime fSpace fSpace2
      hTime hSpace hSpace2 hSmoothTime hSmoothSpace hJoint K hK hBound
      Xeps XepsLeft X2 hXepsInitial hXepsLeft hX2Representation hXepsRepresentation
      Mε hMRepresentation hConv
  · have heq : W = Mε := Set.mem_singleton_iff.mp h
    subst W
    exact Kyprianou.Ch04.exercise45WeightedCutoffSupCauchyV1 P F X hLevy triplet
      hNoGaussian hTriplet hFiltration N Xleft hLeft hNLaw f fTime fSpace fSpace2
      hTime hSpace hSpace2 hSmoothTime hSmoothSpace hJoint K hK hBound
      Xeps XepsLeft X2 hXepsInitial hXepsLeft hX2Representation hXepsRepresentation
      Mε hMRepresentation hConv
