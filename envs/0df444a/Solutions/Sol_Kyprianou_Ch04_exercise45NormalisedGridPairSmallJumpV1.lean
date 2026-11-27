-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45NormalisedGridPairSmallJumpV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:58:34.831966+00:00
-- url     : https://prove2.me/submissions/79dc46bb-2894-458e-b3f3-738a99054fea

import Theorems.Thm_Kyprianou_Ch04_nestedGridPairProbabilityTailV1
import Theorems.Thm_Kyprianou_Ch04_actualNormalisedSmallJumpGridPairBoundV1
import Theorems.Thm_Kyprianou_Ch04_actualPoissonPastMeasurableV1
import Theorems.Thm_Kyprianou_Ch04_actualPoissonFutureIndependenceV1
import Theorems.Thm_Kyprianou_Ch04_boundedSecondDerivativeLipschitzV1
import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false

/-- Apply the actual nested cutoff maximal bound and its vanishing tail. -/
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
              δ ≤ |G (fun s w => Xeps (e l) s w-X2 s w) (Hc0 l) n t w -
                G (fun s w => Xeps (e m) s w-X2 s w) (Hc0 m) n t w|}).toReal ≤ η := by
  intro Ω mΩ P hP F X hLevy triplet hSigma hNoGaussian hTriplet hFiltration N
    Xleft hLeft hNLaw f fTime fSpace fSpace2 hTime hSpace hSpace2 hSmoothTime
    hSmoothSpace hJoint K hK hBound Xeps XepsLeft X2 hXepsInitial hXepsLeft
    hX2Representation hXepsRepresentation Mε hMRepresentation hConv M e he he0 hA hSq hU T
    G H Hc H0 Hc0
  let ν := triplet.levyMeasure
  have hPast := Kyprianou.Ch04.actualPoissonPastMeasurableV1 P ν F X Xleft
    hLevy hFiltration N hLeft hNLaw
  have hFuture := Kyprianou.Ch04.actualPoissonFutureIndependenceV1 P ν F X Xleft
    hLevy hFiltration N hLeft hNLaw
  have hLip (s : NNReal) (x y : ℝ) : |fSpace s x-fSpace s y| ≤ K * |x-y| := by
    have hf : fSpace s = deriv (f s) := funext (hSpace s)
    rw [hf]
    exact Kyprianou.Ch04.boundedSecondDerivativeLipschitzV1 (f s) K y x (hSmoothSpace s)
      (fun v => by rw [← hf,← hSpace2]; exact (hBound s v s.coe_nonneg).2.2.2)
  apply Kyprianou.Ch04.nestedGridPairProbabilityTailV1 P ν triplet.levyMeasure_isLevyMeasure
    K T e (fun m => (he m).1) he0
    (fun m n l δ => {w | ∃ t ≤ T, δ ≤
      |G (fun s w => Xeps (e l) s w-X2 s w) (Hc0 l) n t w -
        G (fun s w => Xeps (e m) s w-X2 s w) (Hc0 m) n t w|})
  intro m n l hl δ hδ
  by_cases hT : T = 0
  · simp [G,hT,not_le.mpr hδ]
  have hT' : 0 < T := pos_iff_ne_zero.mpr hT
  let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
  have hu : Monotone u := by
    intro i j hij
    dsimp [u]
    gcongr
  have huT (k : ℕ) (hk : k ∈ Finset.range n) : u k ≤ T := by
    dsimp [u]
    rw [div_le_iff₀ (by exact_mod_cast (Nat.zero_lt_of_lt (Finset.mem_range.mp hk)))]
    gcongr
    exact_mod_cast (Finset.mem_range.mp hk).le
  exact Kyprianou.Ch04.actualNormalisedSmallJumpGridPairBoundV1 P ν
    triplet.levyMeasure_isLevyMeasure X Xleft X2 (Xeps (e l)) (Xeps (e m))
    (XepsLeft (e l)) (XepsLeft (e m)) F hFiltration N hFuture hPast hNLaw triplet.drift
    (e l) (e m) K (he l).1 hl (he m).2 hK.le hX2Representation
    (hXepsRepresentation _ (he l).1 (he l).2) (hXepsRepresentation _ (he m).1 (he m).2)
    (hXepsLeft _ (he l).1 (he l).2) (hXepsLeft _ (he m).1 (he m).2)
    fSpace hJoint.2.2.1 (fun s x hs => (hBound s x hs).2.2.1) hLip
    T hT' n u hu huT δ hδ
