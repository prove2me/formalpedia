-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45NormalisedGridPairFiniteVariationV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:41:17.298928+00:00
-- url     : https://prove2.me/submissions/1f010a53-1d96-4a75-86ae-18db77d317b3

import Theorems.Thm_Kyprianou_Ch04_physicalFiniteVariationGridEnvelopeV1
import Theorems.Thm_Kyprianou_Ch04_gridPairFromSingleErrorV1
import Theorems.Thm_Kyprianou_Ch04_actualRetainedFiniteAtomsAEV1
import Theorems.Thm_Kyprianou_Ch04_exercise45CutoffEnvelopePairV1
import Theorems.Thm_Kyprianou_Ch04_boundedSecondDerivativeLipschitzV1
import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false

/-- Apply the common finite variation grid envelope to both cutoffs. -/
theorem solution : ∀ {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega)
  [IsProbabilityMeasure P] (F : Filtration NNReal (inferInstance : MeasurableSpace Omega)) (X :
  NNReal -> Omega -> Real) (hLevy : ProbabilityTheory.IsLevyProcess X P) (triplet :
  ProbabilityTheory.LevyKhintchineTriple) [SigmaFinite triplet.levyMeasure] (hNoGaussian :
  triplet.gaussianVariance = 0) (hTriplet : ∀ (t : NNReal) (xi : Real), charFun (P.map (X t)) xi =
  Complex.exp (((t : Real) : Complex) * Kyprianou.Ch01.levyTripleExponent triplet xi)) (hFiltration
  : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F) (N : PoissonRandomMeasure.{0,0,0} P
  triplet.levyMeasure) (Xleft : NNReal -> Omega -> Real) (hLeft : ∀ᵐ omega : Omega ∂P, ∀ t : NNReal,
  0 < t -> Tendsto (fun s : NNReal => X s omega) (nhdsWithin t (Set.Iio t)) (nhds (Xleft t omega)))
  (hNLaw : ∀ᵐ omega : Omega ∂P, N.N omega = Kyprianou.Ch04.pathJumpMeasure X Xleft omega) (f fTime
  fSpace fSpace2 : Real -> Real -> Real) (hTime : ∀ s x : Real, fTime s x = deriv (fun u : Real => f
  u x) s) (hSpace : ∀ s x : Real, fSpace s x = deriv (fun u : Real => f s u) x) (hSpace2 : ∀ s x :
  Real, fSpace2 s x = deriv (fun u : Real => fSpace s u) x) (hSmoothTime : ∀ x : Real, ContDiff Real
  1 (fun s => f s x)) (hSmoothSpace : ∀ s : Real, ContDiff Real 2 (fun x => f s x)) (hJoint :
  ContinuousOn (fun z : Real × Real => f z.1 z.2) (Set.Ici (0 : Real) ×ˢ Set.univ) ∧ ContinuousOn
  (fun z : Real × Real => fTime z.1 z.2) (Set.Ici (0 : Real) ×ˢ Set.univ) ∧ ContinuousOn (fun z :
  Real × Real => fSpace z.1 z.2) (Set.Ici (0 : Real) ×ˢ Set.univ) ∧ ContinuousOn (fun z : Real ×
  Real => fSpace2 z.1 z.2) (Set.Ici (0 : Real) ×ˢ Set.univ)) (K : Real) (hK : 0 < K) (hBound : ∀ s x
  : Real, 0 ≤ s -> |f s x| ≤ K ∧ |fTime s x| ≤ K ∧ |fSpace s x| ≤ K ∧ |fSpace2 s x| ≤ K) (Xeps :
  Real -> NNReal -> Omega -> Real) (XepsLeft : Real -> NNReal -> Omega -> Real) (X2 : NNReal ->
  Omega -> Real) (hXepsInitial : ∀ epsilon omega, 0 < epsilon -> epsilon < 1 -> Xeps epsilon 0 omega
  = X 0 omega) (hXepsLeft : ∀ epsilon : Real, 0 < epsilon -> epsilon < 1 -> ∀ᵐ omega : Omega ∂P, ∀ t
  : NNReal, 0 < t -> Tendsto (fun s : NNReal => Xeps epsilon s omega) (nhdsWithin t (Set.Iio t))
  (nhds (XepsLeft epsilon t omega))) (hX2Representation : ∀ t omega, X2 t omega = triplet.drift * (t
  : Real) + ∫ z in Set.prod (Set.Icc (0 : Real) (t : Real)) {x : Real | 1 ≤ |x|}, z.2 ∂(N.N omega))
  (hXepsRepresentation : ∀ (epsilon : Real), 0 < epsilon -> epsilon < 1 -> ∀ t omega, Xeps epsilon t
  omega = X2 t omega + (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real)) {x : Real | epsilon < |x| ∧
  |x| < 1}, z.2 ∂(N.N omega)) - (t : Real) * (∫ x in {x : Real | epsilon < |x| ∧ |x| < 1}, x
  ∂triplet.levyMeasure)) (Mε : Real -> NNReal -> Omega -> Real) (hMRepresentation : ∀ (epsilon :
  Real), 0 < epsilon -> epsilon < 1 -> ∀ t omega, Mε epsilon t omega = (∫ z in Set.prod (Set.Icc (0
  : Real) (t : Real)) {x : Real | epsilon < |x| ∧ |x| < 1}, z.2 * fSpace z.1 (XepsLeft epsilon
  (Real.toNNReal z.1) omega) ∂(N.N omega)) - (∫ s in Set.Icc (0 : Real) (t : Real), (∫ x in {x :
  Real | epsilon < |x| ∧ |x| < 1}, x * fSpace s (XepsLeft epsilon (Real.toNNReal s) omega)
  ∂triplet.levyMeasure) ∂volume)), (∀ᵐ omega : Omega ∂P, ∀ t : NNReal, Tendsto (fun epsilon : Real
  => Xeps epsilon t omega) (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds (X t omega))) -> ∀ (M : NNReal
  → Omega → Real) (e : ℕ → ℝ), (∀ n, 0 < e n ∧ e n < 1) → Tendsto e atTop (nhds 0) → StronglyAdapted
  F M → (∀ t : NNReal, Integrable (fun w => (M t w)^2) P) → (∀ᵐ w ∂P, ∀ T : NNReal, ∀ δ : ℝ, 0 < δ →
  ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ t : NNReal, t ≤ T → |Xeps (e n) t w - X t w| < δ ∧ |Mε (e n) t w - M t w| <
  δ) → ∀ T : NNReal,
          let G : (NNReal → Omega → ℝ) → (NNReal → Omega → ℝ) →
              ℕ → NNReal → Omega → ℝ := fun Y H n t w =>
            ∑ k ∈ Finset.range n,
              H (T * (k : NNReal) / (n : NNReal)) w *
                (Y (min t (T * ((k+1 : ℕ) : NNReal) / (n : NNReal))) w -
                 Y (min t (T * (k : NNReal) / (n : NNReal))) w)
          let H : NNReal → Omega → ℝ := fun s w => fSpace (s : ℝ) (Xleft s w)
          let Hc : ℕ → NNReal → Omega → ℝ :=
            fun m s w => fSpace (s : ℝ) (XepsLeft (e m) s w)
          let H0 : NNReal → Omega → ℝ := fun s w => if s = 0 then 0 else H s w
          let Hc0 : ℕ → NNReal → Omega → ℝ := fun m s w => if s = 0 then 0 else Hc m s w
          ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η → ∀ᶠ m in atTop,
            ∀ n, ∀ᶠ l in atTop, (P {w | ∃ t ≤ T,
              δ ≤ |G X2 (Hc0 l) n t w - G X2 (Hc0 m) n t w|}).toReal ≤ η := by
  intro Ω mΩ P hP F X hLevy triplet hSigma hNoGaussian hTriplet hFiltration N
    Xleft hLeft hNLaw f fTime fSpace fSpace2 hTime hSpace hSpace2 hSmoothTime
    hSmoothSpace hJoint K hK hBound Xeps XepsLeft X2 hXepsInitial hXepsLeft
    hX2Representation hXepsRepresentation Mε hMRepresentation hConv M e he he0 hA hSq hU T
    G H Hc H0 Hc0
  let ν := triplet.levyMeasure
  obtain ⟨D,E,hD,hE,hDb,hC⟩ := Kyprianou.Ch04.exercise45CutoffEnvelopePairV1
    P F X hLevy triplet hNoGaussian hTriplet hFiltration N Xleft hLeft hNLaw
    f fTime fSpace fSpace2 hTime hSpace hSpace2 hSmoothTime hSmoothSpace hJoint K hK hBound
    Xeps XepsLeft X2 hXepsInitial hXepsLeft hX2Representation hXepsRepresentation
    Mε hMRepresentation hConv M e he he0 hA hSq hU T
  have hLip (s : NNReal) (x y : ℝ) : |fSpace s x-fSpace s y| ≤ K * |x-y| := by
    have hf : fSpace s = deriv (f s) := funext (hSpace s)
    rw [hf]
    exact Kyprianou.Ch04.boundedSecondDerivativeLipschitzV1 (f s) K y x (hSmoothSpace s)
      (fun v => by rw [← hf,← hSpace2]; exact (hBound s v s.coe_nonneg).2.2.2)
  have ha := Kyprianou.Ch04.actualRetainedFiniteAtomsAEV1 P ν triplet.levyMeasure_isLevyMeasure
    N X Xleft hLevy hLeft hNLaw (1/2) (by norm_num)
  apply Kyprianou.Ch04.gridPairFromSingleErrorV1 P T (G X2 H0)
    (fun m => G X2 (Hc0 m))
  exact Kyprianou.Ch04.physicalFiniteVariationGridEnvelopeV1 P ν N T triplet.drift K hK.le
    X Xleft X2 (fun m => Xeps (e m)) (fun m => XepsLeft (e m)) fSpace hLip
    hX2Representation (ha.mono fun w hw => hw T) hLeft
    (ae_all_iff.mpr fun m => hXepsLeft (e m) (he m).1 (he m).2)
    D hD (hDb.mono fun w hw m t ht => (hw m t ht).1)
    (hC.mono fun w hw d hd => Exists.elim (hw d hd) fun n hn =>
      ⟨n,fun m hm => (hn m hm).1⟩)
