-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45FixedCutoffGridProbabilityTransferV5
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:01:43.477231+00:00
-- url     : https://prove2.me/submissions/ecd284c7-7682-4730-8e35-4fca69247528

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise45CutoffStateRegularV5
import Theorems.Thm_Kyprianou_Ch04_exercise45PositiveLeftWeightV5
import Theorems.Thm_Kyprianou_Ch04_exercise45PhysicalGridUCPV5
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false


theorem solution :
  ∀ {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P] (F : Filtration NNReal (inferInstance :
    MeasurableSpace Omega)) (X : NNReal -> Omega -> Real) (hLevy : ProbabilityTheory.IsLevyProcess X P) (triplet :
    ProbabilityTheory.LevyKhintchineTriple) [SigmaFinite triplet.levyMeasure] (hNoGaussian : triplet.gaussianVariance = 0) (hTriplet
    : ∀ (t : NNReal) (xi : Real), charFun (P.map (X t)) xi = Complex.exp (((t : Real) : Complex) * Kyprianou.Ch01.levyTripleExponent
    triplet xi)) (hFiltration : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F) (N : PoissonRandomMeasure.{0,0,0} P
    triplet.levyMeasure) (Xleft : NNReal -> Omega -> Real) (hLeft : ∀ᵐ omega : Omega ∂P, ∀ t : NNReal, 0 < t -> Tendsto (fun s :
    NNReal => X s omega) (nhdsWithin t (Set.Iio t)) (nhds (Xleft t omega))) (hNLaw : ∀ᵐ omega : Omega ∂P, N.N omega =
    Kyprianou.Ch04.pathJumpMeasure X Xleft omega) (f fTime fSpace fSpace2 : Real -> Real -> Real) (hTime : ∀ s x : Real, fTime s x =
    deriv (fun u : Real => f u x) s) (hSpace : ∀ s x : Real, fSpace s x = deriv (fun u : Real => f s u) x) (hSpace2 : ∀ s x : Real,
    fSpace2 s x = deriv (fun u : Real => fSpace s u) x) (hSmoothTime : ∀ x : Real, ContDiff Real 1 (fun s => f s x)) (hSmoothSpace :
    ∀ s : Real, ContDiff Real 2 (fun x => f s x)) (hJoint : ContinuousOn (fun z : Real × Real => f z.1 z.2) (Set.Ici (0 : Real) ×ˢ
    Set.univ) ∧ ContinuousOn (fun z : Real × Real => fTime z.1 z.2) (Set.Ici (0 : Real) ×ˢ Set.univ) ∧ ContinuousOn (fun z : Real ×
    Real => fSpace z.1 z.2) (Set.Ici (0 : Real) ×ˢ Set.univ) ∧ ContinuousOn (fun z : Real × Real => fSpace2 z.1 z.2) (Set.Ici (0 :
    Real) ×ˢ Set.univ)) (K : Real) (hK : 0 < K) (hBound : ∀ s x : Real, 0 ≤ s -> |f s x| ≤ K ∧ |fTime s x| ≤ K ∧ |fSpace s x| ≤ K ∧
    |fSpace2 s x| ≤ K) (Xeps : Real -> NNReal -> Omega -> Real) (XepsLeft : Real -> NNReal -> Omega -> Real) (X2 : NNReal -> Omega
    -> Real) (hXepsInitial : ∀ epsilon omega, 0 < epsilon -> epsilon < 1 -> Xeps epsilon 0 omega = X 0 omega) (hXepsLeft : ∀ epsilon
    : Real, 0 < epsilon -> epsilon < 1 -> ∀ᵐ omega : Omega ∂P, ∀ t : NNReal, 0 < t -> Tendsto (fun s : NNReal => Xeps epsilon s
    omega) (nhdsWithin t (Set.Iio t)) (nhds (XepsLeft epsilon t omega))) (hX2Representation : ∀ t omega, X2 t omega = triplet.drift
    * (t : Real) + ∫ z in Set.prod (Set.Icc (0 : Real) (t : Real)) {x : Real | 1 ≤ |x|}, z.2 ∂(N.N omega)) (hXepsRepresentation : ∀
    (epsilon : Real), 0 < epsilon -> epsilon < 1 -> ∀ t omega, Xeps epsilon t omega = X2 t omega + (∫ z in Set.prod (Set.Icc (0 :
    Real) (t : Real)) {x : Real | epsilon < |x| ∧ |x| < 1}, z.2 ∂(N.N omega)) - (t : Real) * (∫ x in {x : Real | epsilon < |x| ∧ |x|
    < 1}, x ∂triplet.levyMeasure)) (Mε : Real -> NNReal -> Omega -> Real) (hMRepresentation : ∀ (epsilon : Real), 0 < epsilon ->
    epsilon < 1 -> ∀ t omega, Mε epsilon t omega = (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real)) {x : Real | epsilon < |x| ∧ |x|
    < 1}, z.2 * fSpace z.1 (XepsLeft epsilon (Real.toNNReal z.1) omega) ∂(N.N omega)) - (∫ s in Set.Icc (0 : Real) (t : Real), (∫ x
    in {x : Real | epsilon < |x| ∧ |x| < 1}, x * fSpace s (XepsLeft epsilon (Real.toNNReal s) omega) ∂triplet.levyMeasure)
    ∂volume)), (∀ᵐ omega : Omega ∂P, ∀ t : NNReal, Tendsto (fun epsilon : Real => Xeps epsilon t omega) (nhdsWithin (0 : Real)
    (Set.Ioi 0)) (nhds (X t omega))) ->
      let x2Integral : NNReal → Omega → Real := fun t omega => triplet.drift * (∫ s in Set.Icc (0 : Real) (t : Real), fSpace s
        (Xleft s.toNNReal omega)) + ∫ z in Set.Icc (0 : Real) (t : Real) ×ˢ {x : Real | 1 ≤ |x|}, z.2 * fSpace z.1 (Xleft
        z.1.toNNReal omega) ∂(N.N omega)
      ∀ (M : NNReal → Omega → Real) (e : ℕ → ℝ), (∀ n, 0 < e n ∧ e n < 1) → Tendsto e atTop (nhds 0) → StronglyAdapted F M → (∀ t :
        NNReal, Integrable (fun w => (M t w)^2) P) → (∀ᵐ w ∂P, ∀ T : NNReal, ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ t : NNReal, t ≤
        T → |Xeps (e n) t w - X t w| < δ ∧ |Mε (e n) t w - M t w| < δ) →
          ∀ T : NNReal,
          let G : (NNReal → Omega → ℝ) → (NNReal → Omega → ℝ) → ℕ → NNReal → Omega → ℝ := fun Y H n t w => ∑ k ∈ Finset.range n, H
            (T * (k : NNReal) / (n : NNReal)) w * (Y (min t (T * ((k+1 : ℕ) : NNReal) / (n : NNReal))) w - Y (min t (T * (k :
            NNReal) / (n : NNReal))) w)
          let H : NNReal → Omega → ℝ := fun s w => fSpace (s : ℝ) (Xleft s w)
          let Hc : ℕ → NNReal → Omega → ℝ := fun m s w => fSpace (s : ℝ) (XepsLeft (e m) s w)
          let J : ℕ → NNReal → Omega → ℝ := fun m t w => triplet.drift * (∫ s in Set.Icc (0 : ℝ) (t : ℝ), Hc m s.toNNReal w) + (∫ z
            in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}, z.2 * Hc m z.1.toNNReal w ∂(N.N w)) + Mε (e m) t w
          (∀ (m : ℕ), ∀ᵐ w ∂P, ∀ (δ : ℝ), 0 < δ → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ t ≤ T, |G (Xeps (e m)) (Hc m) n t w - J m t w| < δ) →
          ∀ (m : ℕ) (δ : ℝ), 0 < δ → Tendsto (fun n => (P {w | ∃ t ≤ T, δ ≤ |G (Xeps (e m)) (Hc m) n t w - J m t w|}).toReal) atTop
            (nhds 0) := by
  intro Ω m P hP F X hLevy triplet hSigma
    hNoGaussian hTriplet hFiltration N Xleft hLeft hNLaw
    f fTime fSpace fSpace2 hTime hSpace hSpace2
    hSmoothTime hSmoothSpace hJoint
    K hK hBound Xeps XepsLeft X2
    hXepsInitial hXepsLeft
    hX2Representation hXepsRepresentation
    Mε hMRepresentation hConv
  dsimp only
  intro M e he he0 hAdapt hSq hU T
  try dsimp only
  intro hpath k δ hδ
  have hepos := (he k).1
  have helt := (he k).2
  obtain ⟨hmY, hrY⟩ :=
    Kyprianou.Ch04.exercise45CutoffStateRegularV5
      P triplet.levyMeasure
      triplet.levyMeasure_isLevyMeasure
      N X Xleft X2 (Xeps (e k))
      triplet.drift (e k) hepos hNLaw
      hX2Representation
      (hXepsRepresentation (e k) hepos helt)
  have hf : ∀ t : NNReal, Continuous (fSpace (t : ℝ)) := by
    intro t
    have hc : Continuous (fun x : ℝ => ((t : ℝ), x)) :=
      continuous_const.prodMk continuous_id
    exact hJoint.2.2.1.comp_continuous hc
      (fun x => ⟨NNReal.coe_nonneg t, mem_univ x⟩)
  have hmH :=
    Kyprianou.Ch04.exercise45PositiveLeftWeightV5
      P (Xeps (e k)) (XepsLeft (e k)) fSpace
      hmY (hXepsLeft (e k) hepos helt) hf
  have hb : ∀ w, |fSpace 0 (XepsLeft (e k) 0 w)| ≤ K := by
    intro w
    exact (hBound 0 _ le_rfl).2.2.1
  exact Kyprianou.Ch04.exercise45PhysicalGridUCPV5
    P (Xeps (e k))
    (fun s w => fSpace (s : ℝ) (XepsLeft (e k) s w))
    _ hmY hmH hrY T K hK.le hb
    (hpath k) δ hδ
