-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45UniformCutoffPathRegularityV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:30:34.161189+00:00
-- url     : https://prove2.me/submissions/4cf4b688-c697-434a-83c8-9615bece58fe

import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
import Theorems.Thm_Kyprianou_Ch04_actualRetainedFiniteAtomsAEV1
import Theorems.Thm_Kyprianou_Ch04_locallyAffinePathMeasurableV1
import Theorems.Thm_Kyprianou_Ch04_physicalCommonRetainedAtomAffinePathsV1
import Theorems.Thm_Kyprianou_Ch04_leftLimitTimeMeasurableV1
import Theorems.Thm_Kyprianou_Ch04_leftLimitsFromCompactUniformV1
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false
/-- Establish common path measurability and convergence of actual left limits. -/
theorem solution : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (F :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) (X : ℝ≥0 → Ω → ℝ) (hLevy :
    ProbabilityTheory.IsLevyProcess X P) (triplet : ProbabilityTheory.LevyKhintchineTriple)
    [SigmaFinite triplet.levyMeasure] (hNoGaussian : triplet.gaussianVariance = 0) (hTriplet : ∀
    (t : ℝ≥0) (xi : ℝ), charFun (P.map (X t)) xi = Complex.exp (((t : ℝ) : Complex) *
    Kyprianou.Ch01.levyTripleExponent triplet xi)) (hFiltration :
    Kyprianou.Ch03.IsCompletedNaturalFiltration P X F) (N : PoissonRandomMeasure.{0,0,0} P
    triplet.levyMeasure) (Xleft : ℝ≥0 → Ω → ℝ) (hLeft : ∀ᵐ omega : Ω ∂P, ∀ t : ℝ≥0, 0 < t ->
    Tendsto (fun s : ℝ≥0 => X s omega) (nhdsWithin t (Iio t)) (nhds (Xleft t omega))) (hNLaw : ∀ᵐ
    omega : Ω ∂P, N.N omega = Kyprianou.Ch04.pathJumpMeasure X Xleft omega) (f fTime fSpace
    fSpace2 : ℝ → ℝ → ℝ) (hTime : ∀ s x : ℝ, fTime s x = deriv (fun u : ℝ => f u x) s) (hSpace : ∀
    s x : ℝ, fSpace s x = deriv (fun u : ℝ => f s u) x) (hSpace2 : ∀ s x : ℝ, fSpace2 s x = deriv
    (fun u : ℝ => fSpace s u) x) (hSmoothTime : ∀ x : ℝ, ContDiff ℝ 1 (fun s => f s x))
    (hSmoothSpace : ∀ s : ℝ, ContDiff ℝ 2 (fun x => f s x)) (hJoint : ContinuousOn (fun z : ℝ × ℝ
    => f z.1 z.2) (Ici (0 : ℝ) ×ˢ univ) ∧ ContinuousOn (fun z : ℝ × ℝ => fTime z.1 z.2) (Ici (0 :
    ℝ) ×ˢ univ) ∧ ContinuousOn (fun z : ℝ × ℝ => fSpace z.1 z.2) (Ici (0 : ℝ) ×ˢ univ) ∧
    ContinuousOn (fun z : ℝ × ℝ => fSpace2 z.1 z.2) (Ici (0 : ℝ) ×ˢ univ)) (K : ℝ) (hK : 0 < K)
    (hBound : ∀ s x : ℝ, 0 ≤ s -> |f s x| ≤ K ∧ |fTime s x| ≤ K ∧ |fSpace s x| ≤ K ∧ |fSpace2 s x|
    ≤ K) (Xeps : ℝ → ℝ≥0 → Ω → ℝ) (XepsLeft : ℝ → ℝ≥0 → Ω → ℝ) (X2 : ℝ≥0 → Ω → ℝ) (hXepsInitial :
    ∀ epsilon omega, 0 < epsilon → epsilon < 1 -> Xeps epsilon 0 omega = X 0 omega) (hXepsLeft : ∀
    epsilon : ℝ, 0 < epsilon → epsilon < 1 -> ∀ᵐ omega : Ω ∂P, ∀ t : ℝ≥0, 0 < t -> Tendsto (fun s
    : ℝ≥0 => Xeps epsilon s omega) (nhdsWithin t (Iio t)) (nhds (XepsLeft epsilon t omega)))
    (hX2Representation : ∀ t omega, X2 t omega = triplet.drift * (t : ℝ) + ∫ z in Set.prod (Icc (0
    : ℝ) (t : ℝ)) {x : ℝ | 1 ≤ |x|}, z.2 ∂(N.N omega)) (hXepsRepresentation : ∀ (epsilon : ℝ), 0 <
    epsilon → epsilon < 1 → ∀ t omega, Xeps epsilon t omega = X2 t omega + (∫ z in Set.prod (Icc
    (0 : ℝ) (t : ℝ)) {x : ℝ | epsilon < |x| ∧ |x| < 1}, z.2 ∂(N.N omega)) - (t : ℝ) * (∫ x in {x :
    ℝ | epsilon < |x| ∧ |x| < 1}, x ∂triplet.levyMeasure)) (Mε : ℝ → ℝ≥0 → Ω → ℝ)
    (hMRepresentation : ∀ (epsilon : ℝ), 0 < epsilon → epsilon < 1 → ∀ t omega, Mε epsilon t omega
    = (∫ z in Set.prod (Icc (0 : ℝ) (t : ℝ)) {x : ℝ | epsilon < |x| ∧ |x| < 1}, z.2 * fSpace z.1
    (XepsLeft epsilon (Real.toNNReal z.1) omega) ∂(N.N omega)) - (∫ s in Icc (0 : ℝ) (t : ℝ), (∫ x
    in {x : ℝ | epsilon < |x| ∧ |x| < 1}, x * fSpace s (XepsLeft epsilon (Real.toNNReal s) omega)
    ∂triplet.levyMeasure) ∂volume)), (∀ᵐ omega : Ω ∂P, ∀ t : ℝ≥0, Tendsto (fun epsilon : ℝ => Xeps
    epsilon t omega) (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (X t omega))) ->
      let x2Integral : ℝ≥0 → Ω → ℝ := fun t omega =>
        triplet.drift * (∫ s in Icc (0 : ℝ) (t : ℝ), fSpace s (Xleft s.toNNReal omega)) +
        ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|},
          z.2 * fSpace z.1 (Xleft z.1.toNNReal omega) ∂(N.N omega)
      ∀ (M : ℝ≥0 → Ω → ℝ) (e : ℕ → ℝ), (∀ n, 0 < e n ∧ e n < 1) → Tendsto e atTop (nhds 0) →
        StronglyAdapted F M → (∀ t : ℝ≥0, Integrable (fun w => (M t w)^2) P) → (∀ᵐ w ∂P, ∀ T :
        ℝ≥0, ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ t : ℝ≥0, t ≤ T → |Xeps (e n) t w - X t w| < δ
        ∧ |Mε (e n) t w - M t w| < δ) → ∀ᵐ w ∂P, (∀ n : ℕ, Measurable (fun t => Xeps (e n) t w)) ∧
        Measurable (fun t => X t w) ∧ (∀ n : ℕ, Measurable (fun t => XepsLeft (e n) t w)) ∧
        Measurable (fun t => Xleft t w) ∧ (∀ t : ℝ≥0, Tendsto (fun n => Xeps (e n) t w) atTop
        (nhds (X t w))) ∧ (∀ t : ℝ≥0, 0 < t → Tendsto (fun n => XepsLeft (e n) t w) atTop (nhds
        (Xleft t w))) := by
  intro Ω m P hP F X hLevy triplet hSigma hNoGaussian hTriplet hFiltration N
    Xleft hLeft hNLaw f fTime fSpace fSpace2 hTime hSpace hSpace2 hSmoothTime
    hSmoothSpace hJoint K hK hBound Xeps XepsLeft X2 hXepsInitial hXepsLeft
    hX2Representation hXepsRepresentation Mε hMRepresentation hConv I2 M e he he0 hA hSq hU
  have hAtoms := ae_all_iff.mpr (fun n : ℕ =>
    Kyprianou.Ch04.actualRetainedFiniteAtomsAEV1 P triplet.levyMeasure
      triplet.levyMeasure_isLevyMeasure N X Xleft hLevy hLeft hNLaw (e n) (he n).1)
  have hEL := ae_all_iff.mpr (fun n : ℕ => hXepsLeft (e n) (he n).1 (he n).2)
  filter_upwards [hAtoms,hEL,hLeft,hU] with w ha hEL' hL hu
  have hmeas (n : ℕ) : Measurable (fun t => Xeps (e n) t w) := by
    apply Kyprianou.Ch04.locallyAffinePathMeasurableV1 (ι := NNReal)
    intro T
    obtain ⟨S,hs,hR⟩ := ha n T
    let j := fun r : NNReal => X r w - Xleft r w
    let c := ∫ x in {x : ℝ | e n < |x| ∧ |x| < 1}, x ∂triplet.levyMeasure
    refine ⟨S,fun r => (r : ℝ),j,0,triplet.drift-c,?_⟩
    intro t ht
    rw [hXepsRepresentation (e n) (he n).1 (he n).2 t w,hX2Representation t w]
    simp only [zero_add,NNReal.coe_le_coe]
    exact (Kyprianou.Ch04.physicalCommonRetainedAtomAffinePathsV1 (N.N w) T (e n)
      triplet.drift c (he n).2 S j hs hR t ht).2
  have hXlim (t : NNReal) : Tendsto (fun n => Xeps (e n) t w) atTop (nhds (X t w)) := by
    apply Metric.tendsto_nhds.mpr
    intro δ hd
    obtain ⟨J,hJ⟩ := hu t δ hd
    exact eventually_atTop.mpr ⟨J,fun n hn => by
      simpa [Real.dist_eq] using (hJ n hn t le_rfl).1⟩
  have hXm : Measurable (fun t => X t w) := measurable_of_tendsto_metrizable hmeas (tendsto_pi_nhds.mpr hXlim)
  have hl := Kyprianou.Ch04.leftLimitsFromCompactUniformV1
    (fun n t => Xeps (e n) t w) (fun n t => XepsLeft (e n) t w)
    (fun t => X t w) (fun t => Xleft t w) hEL' hL
    (fun T δ hd => by
      obtain ⟨J,hJ⟩ := hu T δ hd
      exact ⟨J,fun n hn t ht => (hJ n hn t ht).1⟩)
  refine ⟨hmeas,hXm,fun n => Kyprianou.Ch04.leftLimitTimeMeasurableV1 _ _
    (hmeas n) (hEL' n),Kyprianou.Ch04.leftLimitTimeMeasurableV1 _ _ hXm hL,hXlim,?_⟩
  intro t ht
  apply Metric.tendsto_nhds.mpr
  intro δ hd
  obtain ⟨J,hJ⟩ := hl t δ hd
  exact eventually_atTop.mpr ⟨J,fun n hn => by
    simpa [Real.dist_eq] using hJ n hn t ht le_rfl⟩
