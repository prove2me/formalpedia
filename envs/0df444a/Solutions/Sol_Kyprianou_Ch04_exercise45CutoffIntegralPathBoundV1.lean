-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45CutoffIntegralPathBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:31:53.482804+00:00
-- url     : https://prove2.me/submissions/2b9fb21d-f535-4628-903f-e2a42be73693

import Theorems.Thm_Kyprianou_Ch04_exercise45UniformCutoffPathRegularityV1
import Theorems.Thm_Kyprianou_Ch04_actualRetainedFiniteAtomsAEV1
import Theorems.Thm_Kyprianou_Ch04_physicalWeightedIntegralErrorRealClockV1
import Theorems.Thm_Kyprianou_Ch04_physicalAbsoluteLedgerMeasurableV1
import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false
theorem solution : ∀ {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
  (F : Filtration NNReal (inferInstance : MeasurableSpace Omega)) (X : NNReal -> Omega -> Real) (hLevy :
  ProbabilityTheory.IsLevyProcess X P) (triplet : ProbabilityTheory.LevyKhintchineTriple) [SigmaFinite
  triplet.levyMeasure] (hNoGaussian : triplet.gaussianVariance = 0) (hTriplet : ∀ (t : NNReal) (xi :
  Real), charFun (P.map (X t)) xi = Complex.exp (((t : Real) : Complex) *
  Kyprianou.Ch01.levyTripleExponent triplet xi)) (hFiltration :
  Kyprianou.Ch03.IsCompletedNaturalFiltration P X F) (N : PoissonRandomMeasure.{0,0,0} P
  triplet.levyMeasure) (Xleft : NNReal -> Omega -> Real) (hLeft : ∀ᵐ omega : Omega ∂P, ∀ t : NNReal, 0 <
  t -> Tendsto (fun s : NNReal => X s omega) (nhdsWithin t (Set.Iio t)) (nhds (Xleft t omega))) (hNLaw :
  ∀ᵐ omega : Omega ∂P, N.N omega = Kyprianou.Ch04.pathJumpMeasure X Xleft omega) (f fTime fSpace fSpace2
  : Real -> Real -> Real) (hTime : ∀ s x : Real, fTime s x = deriv (fun u : Real => f u x) s) (hSpace : ∀
  s x : Real, fSpace s x = deriv (fun u : Real => f s u) x) (hSpace2 : ∀ s x : Real, fSpace2 s x = deriv
  (fun u : Real => fSpace s u) x) (hSmoothTime : ∀ x : Real, ContDiff Real 1 (fun s => f s x))
  (hSmoothSpace : ∀ s : Real, ContDiff Real 2 (fun x => f s x)) (hJoint : ContinuousOn (fun z : Real ×
  Real => f z.1 z.2) (Set.Ici (0 : Real) ×ˢ Set.univ) ∧ ContinuousOn (fun z : Real × Real => fTime z.1
  z.2) (Set.Ici (0 : Real) ×ˢ Set.univ) ∧ ContinuousOn (fun z : Real × Real => fSpace z.1 z.2) (Set.Ici
  (0 : Real) ×ˢ Set.univ) ∧ ContinuousOn (fun z : Real × Real => fSpace2 z.1 z.2) (Set.Ici (0 : Real) ×ˢ
  Set.univ)) (K : Real) (hK : 0 < K) (hBound : ∀ s x : Real, 0 ≤ s -> |f s x| ≤ K ∧ |fTime s x| ≤ K ∧
  |fSpace s x| ≤ K ∧ |fSpace2 s x| ≤ K) (Xeps : Real -> NNReal -> Omega -> Real) (XepsLeft : Real ->
  NNReal -> Omega -> Real) (X2 : NNReal -> Omega -> Real) (hXepsInitial : ∀ epsilon omega, 0 < epsilon ->
  epsilon < 1 -> Xeps epsilon 0 omega = X 0 omega) (hXepsLeft : ∀ epsilon : Real, 0 < epsilon -> epsilon
  < 1 -> ∀ᵐ omega : Omega ∂P, ∀ t : NNReal, 0 < t -> Tendsto (fun s : NNReal => Xeps epsilon s omega)
  (nhdsWithin t (Set.Iio t)) (nhds (XepsLeft epsilon t omega))) (hX2Representation : ∀ t omega, X2 t
  omega = triplet.drift * (t : Real) + ∫ z in Set.prod (Set.Icc (0 : Real) (t : Real)) {x : Real | 1 ≤
  |x|}, z.2 ∂(N.N omega)) (hXepsRepresentation : ∀ (epsilon : Real), 0 < epsilon -> epsilon < 1 -> ∀ t
  omega, Xeps epsilon t omega = X2 t omega + (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real)) {x : Real |
  epsilon < |x| ∧ |x| < 1}, z.2 ∂(N.N omega)) - (t : Real) * (∫ x in {x : Real | epsilon < |x| ∧ |x| <
  1}, x ∂triplet.levyMeasure)) (Mε : Real -> NNReal -> Omega -> Real) (hMRepresentation : ∀ (epsilon :
  Real), 0 < epsilon -> epsilon < 1 -> ∀ t omega, Mε epsilon t omega = (∫ z in Set.prod (Set.Icc (0 :
  Real) (t : Real)) {x : Real | epsilon < |x| ∧ |x| < 1}, z.2 * fSpace z.1 (XepsLeft epsilon
  (Real.toNNReal z.1) omega) ∂(N.N omega)) - (∫ s in Set.Icc (0 : Real) (t : Real), (∫ x in {x : Real |
  epsilon < |x| ∧ |x| < 1}, x * fSpace s (XepsLeft epsilon (Real.toNNReal s) omega) ∂triplet.levyMeasure)
  ∂volume)), (∀ᵐ omega : Omega ∂P, ∀ t : NNReal, Tendsto (fun epsilon : Real => Xeps epsilon t omega)
  (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds (X t omega))) ->
      let x2Integral : NNReal → Omega → Real := fun t omega =>
        triplet.drift * (∫ s in Set.Icc (0 : Real) (t : Real), fSpace s (Xleft s.toNNReal omega)) +
        ∫ z in Set.Icc (0 : Real) (t : Real) ×ˢ {x : Real | 1 ≤ |x|},
          z.2 * fSpace z.1 (Xleft z.1.toNNReal omega) ∂(N.N omega)
      ∀ (M : NNReal → Omega → Real) (e : ℕ → ℝ), (∀ n, 0 < e n ∧ e n < 1) → Tendsto e atTop (nhds 0) →
        StronglyAdapted F M → (∀ t : NNReal, Integrable (fun w => (M t w)^2) P) → (∀ᵐ w ∂P, ∀ T : NNReal,
        ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ t : NNReal, t ≤ T → |Xeps (e n) t w - X t w| < δ ∧ |Mε (e
        n) t w - M t w| < δ) → ∀ T : NNReal,
          let Hc : ℕ → NNReal → Omega → ℝ :=
            fun m s w => fSpace (s : ℝ) (XepsLeft (e m) s w)
          let J : ℕ → NNReal → Omega → ℝ := fun m t w =>
            triplet.drift * (∫ s in Set.Icc (0 : ℝ) (t : ℝ), Hc m s.toNNReal w) +
            (∫ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|},
              z.2 * Hc m z.1.toNNReal w ∂(N.N w)) + Mε (e m) t w
          let C : Omega → ℝ := fun w => K * (|triplet.drift| * (T : ℝ) +
            ∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | 1/2 < |x|}, |z.2| ∂(N.N w))
          Measurable C ∧ (∀ᵐ w ∂P, 0 ≤ C w ∧ ∀ m (d r : ℝ), 0 ≤ d → 0 ≤ r →
            (∀ t ≤ T, |Xeps (e m) t w - X t w| ≤ d) →
            (∀ t ≤ T, |Mε (e m) t w - M t w| ≤ r) →
            ∀ t ≤ T, |J m t w - (x2Integral t w + M t w)| ≤ C w * d + r) := by
  intro Ω mΩ P hP F X hLevy triplet hSigma hNoGaussian hTriplet hFiltration N
    Xleft hLeft hNLaw f fTime fSpace fSpace2 hTime hSpace hSpace2 hSmoothTime
    hSmoothSpace hJoint K hK hBound Xeps XepsLeft X2 hXepsInitial hXepsLeft
    hX2Representation hXepsRepresentation Mε hMRepresentation hConv I2 M e he he0 hA hSq hU T
    Hc J C
  let ν := triplet.levyMeasure
  have hm := Kyprianou.Ch04.physicalAbsoluteLedgerMeasurableV1 P ν N
    (Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | 1/2 < |x|})
    (measurableSet_Icc.prod (measurableSet_lt measurable_const measurable_id.abs))
  refine ⟨measurable_const.mul (measurable_const.add hm),?_⟩
  have ha := Kyprianou.Ch04.actualRetainedFiniteAtomsAEV1 P ν triplet.levyMeasure_isLevyMeasure
    N X Xleft hLevy hLeft hNLaw (1/2) (by norm_num)
  have hp := Kyprianou.Ch04.exercise45UniformCutoffPathRegularityV1 P F X hLevy triplet
    hNoGaussian hTriplet hFiltration N Xleft hLeft hNLaw f fTime fSpace fSpace2
    hTime hSpace hSpace2 hSmoothTime hSmoothSpace hJoint K hK hBound Xeps XepsLeft X2
    hXepsInitial hXepsLeft hX2Representation hXepsRepresentation Mε hMRepresentation
    hConv M e he he0 hA hSq hU
  have hl : ∀ᵐ w ∂P, ∀ m, ∀ t, 0 < t →
      Tendsto (fun s => Xeps (e m) s w) (nhdsWithin t (Iio t)) (nhds (XepsLeft (e m) t w)) :=
    ae_all_iff.mpr fun m => hXepsLeft (e m) (he m).1 (he m).2
  filter_upwards [ha,hp,hl,hLeft] with w hw hp' hl' hL
  obtain ⟨S,hS,hR⟩ := hw T
  have hC0 : 0 ≤ C w := mul_nonneg hK.le (add_nonneg (by positivity)
    (integral_nonneg fun z => abs_nonneg z.2))
  refine ⟨hC0,?_⟩
  intro m d r hd hr hD hE t ht
  have hg' (s : ℝ) : Differentiable ℝ (fSpace s) := by
    have heq : fSpace s = deriv (f s) := funext (hSpace s)
    rw [heq]
    exact (hSmoothSpace s).differentiable_deriv_two
  exact Kyprianou.Ch04.physicalWeightedIntegralErrorRealClockV1 (N.N w) T S
    (fun r => X r w - Xleft r w) (fun t => Xeps (e m) t w) (fun t => X t w)
    (fun t => XepsLeft (e m) t w) (fun t => Xleft t w) fSpace
    triplet.drift K d r hd hK.le hS hR (hp'.2.2.1 m) hp'.2.2.2.1
    (hl' m) hL hD hJoint.2.2.1 hg' (fun s x hs => (hBound s x hs).2.2.1)
    (fun s x hs => by rw [← hSpace2 s x]; exact (hBound s x hs).2.2.2)
    (fun t => Mε (e m) t w) (fun t => M t w) hE t ht
