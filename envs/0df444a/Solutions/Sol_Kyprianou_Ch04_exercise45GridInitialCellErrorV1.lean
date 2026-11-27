-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45GridInitialCellErrorV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:31:12.311544+00:00
-- url     : https://prove2.me/submissions/4f05b075-6b3d-4c2e-849c-1fb19812a6f3

import Theorems.Thm_Kyprianou_Ch04_clippedGridInitialDifferenceProbabilityV1
import Theorems.Thm_Kyprianou_Ch04_actualPoissonPastMeasurableV1
import Theorems.Thm_Kyprianou_Ch04_actualCutoffAdaptedV1
import Theorems.Thm_Kyprianou_Ch04_actualCutoffStateRightV1
import Theorems.Thm_Kyprianou_Ch04_pathJumpMeasureZeroTimeV1
import Theorems.Thm_Kyprianou_Ch03_completedNaturalCoordinateAdaptedV1
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
  Xeps epsilon t omega) (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds (X t omega))) -> ∀ (M : NNReal →
  Omega → Real) (e : ℕ → ℝ), (∀ n, 0 < e n ∧ e n < 1) → Tendsto e atTop (nhds 0) → StronglyAdapted F
  M → (∀ t : NNReal, Integrable (fun w => (M t w)^2) P) → (∀ᵐ w ∂P, ∀ T : NNReal, ∀ δ : ℝ, 0 < δ → ∃
  n₀ : ℕ, ∀ n ≥ n₀, ∀ t : NNReal, t ≤ T → |Xeps (e n) t w - X t w| < δ ∧ |Mε (e n) t w - M t w| < δ)
  → ∀ T : NNReal,
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
          ∀ m, ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop,
            (P {w | ∃ t ≤ T, δ ≤ |(G X H n t w - G X H0 n t w) -
              (G (Xeps (e m)) (Hc m) n t w - G (Xeps (e m)) (Hc0 m) n t w)|}).toReal ≤ η := by
  intro Ω mΩ P hP F X hLevy triplet hSigma hNoGaussian hTriplet hFiltration N
    Xleft hLeft hNLaw f fTime fSpace fSpace2 hTime hSpace hSpace2 hSmoothTime
    hSmoothSpace hJoint K hK hBound Xeps XepsLeft X2 hXepsInitial hXepsLeft
    hX2Representation hXepsRepresentation Mε hMRepresentation hConv M e he he0 hA hSq hU T
    G H Hc H0 Hc0 m
  by_cases ht : T = 0
  · intro δ hδ η hη
    apply Eventually.of_forall
    intro n
    have hz (Y W : NNReal → Ω → ℝ) (t : NNReal) (w : Ω) : G Y W n t w = 0 := by
      simp [G,ht]
    simp [hz,not_le_of_gt hδ,hη.le]
  let ν := triplet.levyMeasure
  have hp := Kyprianou.Ch04.actualPoissonPastMeasurableV1 P ν F X Xleft hLevy
    hFiltration N hLeft hNLaw
  have hz : ∀ᵐ w ∂P, N.N w (({0} : Set ℝ) ×ˢ (univ : Set ℝ)) = 0 := by
    filter_upwards [hNLaw] with w hw
    rw [hw]
    exact Kyprianou.Ch04.pathJumpMeasureZeroTimeV1 X Xleft w
  have hX := Kyprianou.Ch03.completedNaturalCoordinateAdaptedV1 P X F hFiltration
  have hY := Kyprianou.Ch04.actualCutoffAdaptedV1 P ν F N hp triplet.drift (e m)
    (Xeps (e m)) X2 hX2Representation (hXepsRepresentation (e m) (he m).1 (he m).2)
  exact Kyprianou.Ch04.clippedGridInitialDifferenceProbabilityV1 P X (Xeps (e m)) H (Hc m)
    K hK.le (fun w => (hBound 0 (Xleft 0 w) le_rfl).2.2.1)
    (fun w => (hBound 0 (XepsLeft (e m) 0 w) le_rfl).2.2.1)
    (fun t => ((hX t).mono (F.le t) le_rfl).aemeasurable)
    (fun t => ((hY t).mono (F.le t) le_rfl).aemeasurable)
    (hLevy.cadlag_ae.mono fun w hw t => (hw t).1)
    (Kyprianou.Ch04.actualCutoffStateRightV1 P ν triplet.levyMeasure_isLevyMeasure N
      (Xeps (e m)) X2 triplet.drift (e m) (he m).1 hz hX2Representation
      (hXepsRepresentation (e m) (he m).1 (he m).2))
    T (pos_iff_ne_zero.mpr ht)
