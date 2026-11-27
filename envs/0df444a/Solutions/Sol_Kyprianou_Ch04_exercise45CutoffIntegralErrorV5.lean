-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45CutoffIntegralErrorV5
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:17:09.780203+00:00
-- url     : https://prove2.me/submissions/b7538953-058c-4e77-94d4-7480351a4319

import Theorems.Thm_Kyprianou_Ch04_exercise45CutoffEnvelopePairV1
import Theorems.Thm_Kyprianou_Ch04_exercise45CutoffIntegralPathBoundV1
import Theorems.Thm_Kyprianou_Ch04_weightedCompactEnvelopeProbabilityV1
import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false
theorem solution : ∀ {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure
  P] (F : Filtration NNReal (inferInstance : MeasurableSpace Omega)) (X : NNReal -> Omega -> Real)
  (hLevy : ProbabilityTheory.IsLevyProcess X P) (triplet : ProbabilityTheory.LevyKhintchineTriple)
  [SigmaFinite triplet.levyMeasure] (hNoGaussian : triplet.gaussianVariance = 0) (hTriplet : ∀ (t :
  NNReal) (xi : Real), charFun (P.map (X t)) xi = Complex.exp (((t : Real) : Complex) *
  Kyprianou.Ch01.levyTripleExponent triplet xi)) (hFiltration :
  Kyprianou.Ch03.IsCompletedNaturalFiltration P X F) (N : PoissonRandomMeasure.{0,0,0} P
  triplet.levyMeasure) (Xleft : NNReal -> Omega -> Real) (hLeft : ∀ᵐ omega : Omega ∂P, ∀ t : NNReal,
  0 < t -> Tendsto (fun s : NNReal => X s omega) (nhdsWithin t (Set.Iio t)) (nhds (Xleft t omega)))
  (hNLaw : ∀ᵐ omega : Omega ∂P, N.N omega = Kyprianou.Ch04.pathJumpMeasure X Xleft omega) (f fTime
  fSpace fSpace2 : Real -> Real -> Real) (hTime : ∀ s x : Real, fTime s x = deriv (fun u : Real => f
  u x) s) (hSpace : ∀ s x : Real, fSpace s x = deriv (fun u : Real => f s u) x) (hSpace2 : ∀ s x :
  Real, fSpace2 s x = deriv (fun u : Real => fSpace s u) x) (hSmoothTime : ∀ x : Real, ContDiff Real
  1 (fun s => f s x)) (hSmoothSpace : ∀ s : Real, ContDiff Real 2 (fun x => f s x)) (hJoint :
  ContinuousOn (fun z : Real × Real => f z.1 z.2) (Set.Ici (0 : Real) ×ˢ Set.univ) ∧ ContinuousOn
  (fun z : Real × Real => fTime z.1 z.2) (Set.Ici (0 : Real) ×ˢ Set.univ) ∧ ContinuousOn (fun z :
  Real × Real => fSpace z.1 z.2) (Set.Ici (0 : Real) ×ˢ Set.univ) ∧ ContinuousOn (fun z : Real × Real
  => fSpace2 z.1 z.2) (Set.Ici (0 : Real) ×ˢ Set.univ)) (K : Real) (hK : 0 < K) (hBound : ∀ s x :
  Real, 0 ≤ s -> |f s x| ≤ K ∧ |fTime s x| ≤ K ∧ |fSpace s x| ≤ K ∧ |fSpace2 s x| ≤ K) (Xeps : Real
  -> NNReal -> Omega -> Real) (XepsLeft : Real -> NNReal -> Omega -> Real) (X2 : NNReal -> Omega ->
  Real) (hXepsInitial : ∀ epsilon omega, 0 < epsilon -> epsilon < 1 -> Xeps epsilon 0 omega = X 0
  omega) (hXepsLeft : ∀ epsilon : Real, 0 < epsilon -> epsilon < 1 -> ∀ᵐ omega : Omega ∂P, ∀ t :
  NNReal, 0 < t -> Tendsto (fun s : NNReal => Xeps epsilon s omega) (nhdsWithin t (Set.Iio t)) (nhds
  (XepsLeft epsilon t omega))) (hX2Representation : ∀ t omega, X2 t omega = triplet.drift * (t :
  Real) + ∫ z in Set.prod (Set.Icc (0 : Real) (t : Real)) {x : Real | 1 ≤ |x|}, z.2 ∂(N.N omega))
  (hXepsRepresentation : ∀ (epsilon : Real), 0 < epsilon -> epsilon < 1 -> ∀ t omega, Xeps epsilon t
  omega = X2 t omega + (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real)) {x : Real | epsilon < |x| ∧
  |x| < 1}, z.2 ∂(N.N omega)) - (t : Real) * (∫ x in {x : Real | epsilon < |x| ∧ |x| < 1}, x
  ∂triplet.levyMeasure)) (Mε : Real -> NNReal -> Omega -> Real) (hMRepresentation : ∀ (epsilon :
  Real), 0 < epsilon -> epsilon < 1 -> ∀ t omega, Mε epsilon t omega = (∫ z in Set.prod (Set.Icc (0 :
  Real) (t : Real)) {x : Real | epsilon < |x| ∧ |x| < 1}, z.2 * fSpace z.1 (XepsLeft epsilon
  (Real.toNNReal z.1) omega) ∂(N.N omega)) - (∫ s in Set.Icc (0 : Real) (t : Real), (∫ x in {x : Real
  | epsilon < |x| ∧ |x| < 1}, x * fSpace s (XepsLeft epsilon (Real.toNNReal s) omega)
  ∂triplet.levyMeasure) ∂volume)), (∀ᵐ omega : Omega ∂P, ∀ t : NNReal, Tendsto (fun epsilon : Real =>
  Xeps epsilon t omega) (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds (X t omega))) ->
      let x2Integral : NNReal → Omega → Real := fun t omega =>
        triplet.drift * (∫ s in Set.Icc (0 : Real) (t : Real), fSpace s (Xleft s.toNNReal omega)) +
        ∫ z in Set.Icc (0 : Real) (t : Real) ×ˢ {x : Real | 1 ≤ |x|},
          z.2 * fSpace z.1 (Xleft z.1.toNNReal omega) ∂(N.N omega)
      ∀ (M : NNReal → Omega → Real) (e : ℕ → ℝ),
          (∀ n, 0 < e n ∧ e n < 1) →
          Tendsto e atTop (nhds 0) →
          StronglyAdapted F M →
          (∀ t : NNReal, Integrable (fun w => (M t w)^2) P) →
          (∀ᵐ w ∂P, ∀ T : NNReal, ∀ δ : ℝ, 0 < δ →
            ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ t : NNReal, t ≤ T →
              |Xeps (e n) t w - X t w| < δ ∧ |Mε (e n) t w - M t w| < δ) →
          ∀ T : NNReal,
          let G : (NNReal → Omega → ℝ) → (NNReal → Omega → ℝ) →
              ℕ → NNReal → Omega → ℝ := fun Y H n t w =>
            ∑ k ∈ Finset.range n,
              H (T * (k : NNReal) / (n : NNReal)) w *
                (Y (min t (T * ((k+1 : ℕ) : NNReal) / (n : NNReal))) w -
                 Y (min t (T * (k : NNReal) / (n : NNReal))) w)
          let H : NNReal → Omega → ℝ := fun s w => fSpace (s : ℝ) (Xleft s w)
          let Hc : ℕ → NNReal → Omega → ℝ :=
            fun m s w => fSpace (s : ℝ) (XepsLeft (e m) s w)
          let J : ℕ → NNReal → Omega → ℝ := fun m t w =>
            triplet.drift * (∫ s in Set.Icc (0 : ℝ) (t : ℝ), Hc m s.toNNReal w) +
            (∫ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|},
              z.2 * Hc m z.1.toNNReal w ∂(N.N w)) + Mε (e m) t w
          ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η → ∀ᶠ m in atTop,
            (P {w | ∃ t ≤ T,
              δ ≤ |J m t w - (x2Integral t w + M t w)|}).toReal ≤ η := by
  intro Ω mΩ P hP F X hLevy triplet hSigma hNoGaussian hTriplet hFiltration N
    Xleft hLeft hNLaw f fTime fSpace fSpace2 hTime hSpace hSpace2 hSmoothTime
    hSmoothSpace hJoint K hK hBound Xeps XepsLeft X2 hXepsInitial hXepsLeft
    hX2Representation hXepsRepresentation Mε hMRepresentation hConv I2 M e he he0 hA hSq hU T
    G H Hc J δ hδ η hη
  obtain ⟨D,E,hD,hE,hDE,hconv⟩ :=
    Kyprianou.Ch04.exercise45CutoffEnvelopePairV1 P F X hLevy triplet hNoGaussian hTriplet
      hFiltration N Xleft hLeft hNLaw f fTime fSpace fSpace2 hTime hSpace hSpace2 hSmoothTime
      hSmoothSpace hJoint K hK hBound Xeps XepsLeft X2 hXepsInitial hXepsLeft hX2Representation
      hXepsRepresentation Mε hMRepresentation hConv M e he he0 hA hSq hU T
  obtain ⟨hC,hbound⟩ :=
    Kyprianou.Ch04.exercise45CutoffIntegralPathBoundV1 P F X hLevy triplet hNoGaussian hTriplet
      hFiltration N Xleft hLeft hNLaw f fTime fSpace fSpace2 hTime hSpace hSpace2 hSmoothTime
      hSmoothSpace hJoint K hK hBound Xeps XepsLeft X2 hXepsInitial hXepsLeft hX2Representation
      hXepsRepresentation Mε hMRepresentation hConv M e he he0 hA hSq hU T
  let C : Ω → ℝ := fun w => K * (|triplet.drift| * (T : ℝ) +
    ∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | 1/2 < |x|}, |z.2| ∂(N.N w))
  have hb : ∀ᵐ w ∂P, 0 ≤ C w ∧ ∀ m, D m w ≠ ⊤ → E m w ≠ ⊤ →
      ∀ t ≤ T, |J m t w - (I2 t w + M t w)| ≤
        C w * (D m w).toReal + (E m w).toReal := by
    filter_upwards [hbound,hDE] with w hw hd
    refine ⟨hw.1,fun m hdm hem => ?_⟩
    exact hw.2 m _ _ ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      (fun t ht => by
        simpa only [ENNReal.toReal_ofReal (abs_nonneg _)] using
          ENNReal.toReal_mono hdm (hd m t ht).1)
      (fun t ht => by
        simpa only [ENNReal.toReal_ofReal (abs_nonneg _)] using
          ENNReal.toReal_mono hem (hd m t ht).2)
  have hl := Kyprianou.Ch04.weightedCompactEnvelopeProbabilityV1 P
    (fun m t w => J m t w - (I2 t w + M t w)) T C D E hC hD hE hb hconv δ hδ
  exact (hl.eventually (Iio_mem_nhds hη)).mono (fun m hm => hm.le)
