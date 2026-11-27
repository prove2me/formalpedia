-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45CutoffEnvelopePairV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:21:27.896711+00:00
-- url     : https://prove2.me/submissions/4e340ef9-afb1-4a90-b8eb-a0b9caa304b1

import Theorems.Thm_Kyprianou_Ch04_compactUniformSequenceEnvelopeV1
import Theorems.Thm_Kyprianou_Ch04_actualPoissonPastMeasurableV1
import Theorems.Thm_Kyprianou_Ch04_actualCutoffAdaptedV1
import Theorems.Thm_Kyprianou_Ch04_actualCutoffStateRightV1
import Theorems.Thm_Kyprianou_Ch04_pathJumpMeasureZeroTimeV1
import Theorems.Thm_Kyprianou_Ch04_exercise45FiniteCutoffMartingaleV1
import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false
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
  δ) → ∀ T : NNReal, ∃ D E : ℕ → Omega → ℝ≥0∞, (∀ m, Measurable (D m)) ∧ (∀ m, Measurable (E m)) ∧
  (∀ᵐ w ∂P, ∀ m t, t ≤ T → ENNReal.ofReal |Xeps (e m) t w - X t w| ≤ D m w ∧ ENNReal.ofReal |Mε (e
  m) t w - M t w| ≤ E m w) ∧ (∀ᵐ w ∂P, ∀ d : ℝ, 0 < d → ∃ N : ℕ, ∀ m ≥ N, D m w ≤ ENNReal.ofReal d ∧
  E m w ≤ ENNReal.ofReal d) := by
  intro Ω mΩ P hP F X hLevy triplet hSigma hNoGaussian hTriplet hFiltration N
    Xleft hLeft hNLaw f fTime fSpace fSpace2 hTime hSpace hSpace2 hSmoothTime
    hSmoothSpace hJoint K hK hBound Xeps XepsLeft X2 hXepsInitial hXepsLeft
    hX2Representation hXepsRepresentation Mε hMRepresentation hConv M e he he0 hA hSq hU T
  let ν := triplet.levyMeasure
  have hp := Kyprianou.Ch04.actualPoissonPastMeasurableV1 P ν F X Xleft hLevy
    hFiltration N hLeft hNLaw
  have hz : ∀ᵐ w ∂P, N.N w (({0} : Set ℝ) ×ˢ (univ : Set ℝ)) = 0 := by
    filter_upwards [hNLaw] with w hw
    rw [hw]
    exact Kyprianou.Ch04.pathJumpMeasureZeroTimeV1 X Xleft w
  have hXm (m : ℕ) (t : NNReal) : AEMeasurable (Xeps (e m) t) P :=
    (((Kyprianou.Ch04.actualCutoffAdaptedV1 P ν F N hp triplet.drift (e m)
      (Xeps (e m)) X2 hX2Representation
      (hXepsRepresentation (e m) (he m).1 (he m).2)) t).mono (F.le t) le_rfl).aemeasurable
  have hXr (m : ℕ) := Kyprianou.Ch04.actualCutoffStateRightV1 P ν
    triplet.levyMeasure_isLevyMeasure N (Xeps (e m)) X2 triplet.drift (e m)
    (he m).1 hz hX2Representation (hXepsRepresentation (e m) (he m).1 (he m).2)
  have hm (m : ℕ) : Martingale (Mε (e m)) F P ∧
      (∀ᵐ w ∂P, ∀ t, ContinuousWithinAt (fun s => Mε (e m) s w) (Ici t) t) := by
    have h := Kyprianou.Ch04.exercise45FiniteCutoffMartingaleV1 P F X hLevy triplet
      hNoGaussian hTriplet hFiltration N Xleft hLeft hNLaw f fTime fSpace fSpace2
      hTime hSpace hSpace2 hSmoothTime hSmoothSpace hJoint K hK hBound Xeps XepsLeft X2
      hXepsInitial hXepsLeft hX2Representation hXepsRepresentation (e m) (he m).1 (he m).2
    have eq : Mε (e m) = (fun (t : NNReal) w =>
      (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | e m < |x| ∧ |x| < 1},
        z.2 * fSpace z.1 (XepsLeft (e m) z.1.toNNReal w) ∂(N.N w)) -
      (∫ s in Icc (0 : ℝ) (t : ℝ), (∫ x in {x : ℝ | e m < |x| ∧ |x| < 1},
        x * fSpace s (XepsLeft (e m) s.toNNReal w) ∂ν) ∂volume)) := funext fun t => funext fun w =>
      hMRepresentation (e m) (he m).1 (he m).2 t w
    rw [eq]
    exact ⟨h.1,h.2.2.mono (fun w hw t => continuousWithinAt_Ioi_iff_Ici.mp (hw t))⟩
  obtain ⟨D,hD,hDb⟩ := Kyprianou.Ch04.compactUniformSequenceEnvelopeV1 P
    (fun m => Xeps (e m)) X T hXm hXr
    (hU.mono fun w hw d hd => Exists.elim (hw T d hd) fun n hn =>
      ⟨n,fun m hm t ht => (hn m hm t ht).1⟩)
  obtain ⟨E,hE,hEb⟩ := Kyprianou.Ch04.compactUniformSequenceEnvelopeV1 P
    (fun m => Mε (e m)) M T
    (fun m t => (((hm m).1.stronglyAdapted t).mono (F.le t)).measurable.aemeasurable)
    (fun m => (hm m).2)
    (hU.mono fun w hw d hd => Exists.elim (hw T d hd) fun n hn =>
      ⟨n,fun m hm t ht => (hn m hm t ht).2⟩)
  refine ⟨D,E,hD,hE,?_,?_⟩
  · filter_upwards [hDb,hEb] with w hD' hE'
    exact fun m t ht => ⟨hD'.1 m t ht,hE'.1 m t ht⟩
  · filter_upwards [hDb,hEb] with w hD' hE'
    intro d hd
    obtain ⟨n,hn⟩ := hD'.2 d hd
    obtain ⟨k,hk⟩ := hE'.2 d hd
    exact ⟨max n k,fun m hm => ⟨hn m ((le_max_left n k).trans hm),
      hk m ((le_max_right n k).trans hm)⟩⟩
