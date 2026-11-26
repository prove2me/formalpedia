-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45ActualCutoffRawEnergyV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:11:09.725545+00:00
-- url     : https://prove2.me/submissions/1b3a2d1e-6444-4745-9d26-3736cc279827

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_actualPoissonFutureIndependenceV1
import Theorems.Thm_Kyprianou_Ch04_actualPoissonPastMeasurableV1
import Theorems.Thm_Kyprianou_Ch04_actualCutoffAdaptedV1
import Theorems.Thm_Kyprianou_Ch04_adaptedCutoffRawEnergyV1
open MeasureTheory ProbabilityTheory Filter ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Reduce the actual cutoff energy to adapted states and their physical integrals. -/
theorem solution :
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal -> Omega -> Real)
    (hLevy : ProbabilityTheory.IsLevyProcess X P)
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    [SigmaFinite triplet.levyMeasure]
    (hNoGaussian : triplet.gaussianVariance = 0)
    (hTriplet : ∀ (t : NNReal) (xi : Real),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : Real) : Complex) *
          Kyprianou.Ch01.levyTripleExponent triplet xi))
    (hFiltration : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (N : PoissonRandomMeasure.{0,0,0}
      P triplet.levyMeasure)
    (Xleft : NNReal -> Omega -> Real)
    (hLeft : ∀ᵐ omega : Omega ∂P, ∀ t : NNReal, 0 < t ->
      Tendsto (fun s : NNReal => X s omega)
        (nhdsWithin t (Set.Iio t)) (nhds (Xleft t omega)))
    (hNLaw : ∀ᵐ omega : Omega ∂P,
      N.N omega = Kyprianou.Ch04.pathJumpMeasure X Xleft omega)
    (f fTime fSpace fSpace2 : Real -> Real -> Real)
    (hTime : ∀ s x : Real,
      fTime s x = deriv (fun u : Real => f u x) s)
    (hSpace : ∀ s x : Real,
      fSpace s x = deriv (fun u : Real => f s u) x)
    (hSpace2 : ∀ s x : Real,
      fSpace2 s x = deriv (fun u : Real => fSpace s u) x)
    (hSmoothTime : ∀ x : Real, ContDiff Real 1 (fun s => f s x))
    (hSmoothSpace : ∀ s : Real, ContDiff Real 2 (fun x => f s x))
    (hJoint : ContinuousOn (fun z : Real × Real => f z.1 z.2)
        (Set.Ici (0 : Real) ×ˢ Set.univ) ∧
      ContinuousOn (fun z : Real × Real => fTime z.1 z.2)
        (Set.Ici (0 : Real) ×ˢ Set.univ) ∧
      ContinuousOn (fun z : Real × Real => fSpace z.1 z.2)
        (Set.Ici (0 : Real) ×ˢ Set.univ) ∧
      ContinuousOn (fun z : Real × Real => fSpace2 z.1 z.2)
        (Set.Ici (0 : Real) ×ˢ Set.univ))
    (K : Real) (hK : 0 < K)
    (hBound : ∀ s x : Real, 0 ≤ s ->
      |f s x| ≤ K ∧ |fTime s x| ≤ K ∧
      |fSpace s x| ≤ K ∧ |fSpace2 s x| ≤ K)
    (Xeps : Real -> NNReal -> Omega -> Real)
    (XepsLeft : Real -> NNReal -> Omega -> Real)
    (X2 : NNReal -> Omega -> Real)
    (hXepsInitial : ∀ epsilon omega, 0 < epsilon -> epsilon < 1 ->
      Xeps epsilon 0 omega = X 0 omega)
    (hXepsLeft : ∀ epsilon : Real, 0 < epsilon -> epsilon < 1 ->
      ∀ᵐ omega : Omega ∂P, ∀ t : NNReal, 0 < t ->
        Tendsto (fun s : NNReal => Xeps epsilon s omega)
          (nhdsWithin t (Set.Iio t))
          (nhds (XepsLeft epsilon t omega)))
    (hX2Representation : ∀ t omega,
      X2 t omega =
        triplet.drift * (t : Real) +
        ∫ z in Set.prod (Set.Icc (0 : Real) (t : Real))
                   {x : Real | 1 ≤ |x|}, z.2 ∂(N.N omega))
    (hXepsRepresentation : ∀ (epsilon : Real),
      0 < epsilon -> epsilon < 1 -> ∀ t omega,
      Xeps epsilon t omega = X2 t omega +
        (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real))
             {x : Real | epsilon < |x| ∧ |x| < 1},
          z.2 ∂(N.N omega)) -
        (t : Real) * (∫ x in {x : Real | epsilon < |x| ∧ |x| < 1},
          x ∂triplet.levyMeasure)),
    ∀ (T : NNReal), 0 < T ->
          ∀ (M : Real -> NNReal -> Omega -> Real),
            (∀ epsilon : Real, 0 < epsilon -> epsilon < 1 ->
              (∀ t omega, M epsilon t omega = (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real))
        {x : Real | epsilon < |x| ∧ |x| < 1},
        z.2 * fSpace z.1 (XepsLeft epsilon (Real.toNNReal z.1) omega)
        ∂(N.N omega)) -
      (∫ s in Set.Icc (0 : Real) (t : Real),
        (∫ x in {x : Real | epsilon < |x| ∧ |x| < 1},
          x * fSpace s (XepsLeft epsilon (Real.toNNReal s) omega)
          ∂triplet.levyMeasure) ∂volume)) ∧
              MeasureTheory.Martingale (M epsilon) F P) ->
    ∀ a b : ℝ, 0 < a → a < b → b < 1 →
      (∫ ω, (M a T ω - M b T ω)^2 ∂P) ≤
        (∫ ω, ∫ s in Set.Ioc (0 : ℝ) (T : ℝ),
          ∫ z, (({w : ℝ | a < |w| ∧ |w| < 1}).indicator
              (fun w => w * fSpace s (XepsLeft a s.toNNReal ω)) z -
            ({w : ℝ | b < |w| ∧ |w| < 1}).indicator
              (fun w => w * fSpace s (XepsLeft b s.toNNReal ω)) z)^2
              ∂triplet.levyMeasure ∂volume ∂P) := by
  intro Ω m P hP F X hLevy triplet hSigma hNoGaussian hTriplet hFiltration N
    Xleft hLeft hNLaw f fTime fSpace fSpace2 hTime hSpace hSpace2 hSmoothTime
    hSmoothSpace hJoint K hK hBound Xeps XepsLeft X2 hXepsInitial hXepsLeft
    hX2Representation hXepsRepresentation T hT M hM a b ha hab hb
  have hFuture := Kyprianou.Ch04.actualPoissonFutureIndependenceV1
    P triplet.levyMeasure F X Xleft hLevy hFiltration N hLeft hNLaw
  have hPast := Kyprianou.Ch04.actualPoissonPastMeasurableV1
    P triplet.levyMeasure F X Xleft hLevy hFiltration N hLeft hNLaw
  have hAdapt (e : ℝ) (he : 0 < e) (he1 : e < 1) : Adapted F (Xeps e) :=
    Kyprianou.Ch04.actualCutoffAdaptedV1 P triplet.levyMeasure F N hPast
      triplet.drift e (Xeps e) X2 hX2Representation (hXepsRepresentation e he he1)
  exact Kyprianou.Ch04.adaptedCutoffRawEnergyV1 P F X triplet hFiltration N hFuture hPast
    fSpace hJoint.2.2.1 K hK (fun s x hs => (hBound s x hs).2.2.1)
    Xeps XepsLeft hAdapt hXepsLeft T hT M hM a b ha hab hb
