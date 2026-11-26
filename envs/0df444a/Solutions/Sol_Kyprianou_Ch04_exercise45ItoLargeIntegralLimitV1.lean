-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45ItoLargeIntegralLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:19:48.187861+00:00
-- url     : https://prove2.me/submissions/a3596f0f-59ca-43bf-bb03-6207726d6025

import Theorems.Thm_Kyprianou_Ch04_exercise45UniformCutoffPathRegularityV1
import Theorems.Thm_Kyprianou_Ch04_actualRetainedFiniteAtomsAEV1
import Theorems.Thm_Kyprianou_Ch04_pathTimeWeightDCTV1
import Theorems.Thm_Kyprianou_Ch04_finiteAtomWeightLimitV1
import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false
/-- Drift dominated convergence and finite atom termwise convergence. -/
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
        ∧ |Mε (e n) t w - M t w| < δ) → ∀ᵐ w ∂P, ∀ t : ℝ≥0, Tendsto (fun n => triplet.drift * (∫ s
        in Icc (0 : ℝ) (t : ℝ), fSpace s (XepsLeft (e n) s.toNNReal w)) + ∫ z in Icc (0 : ℝ) (t :
        ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}, z.2 * fSpace z.1 (XepsLeft (e n) z.1.toNNReal w) ∂(N.N w)) atTop
        (nhds (x2Integral t w)) := by
  intro Ω m P hP F X hLevy triplet hSigma hNoGaussian hTriplet hFiltration N
    Xleft hLeft hNLaw f fTime fSpace fSpace2 hTime hSpace hSpace2 hSmoothTime
    hSmoothSpace hJoint K hK hBound Xeps XepsLeft X2 hXepsInitial hXepsLeft
    hX2Representation hXepsRepresentation Mε hMRepresentation hConv I2 M e he he0 hA hSq hU
  have hp := Kyprianou.Ch04.exercise45UniformCutoffPathRegularityV1 P F X hLevy triplet hNoGaussian hTriplet hFiltration N
    Xleft hLeft hNLaw f fTime fSpace fSpace2 hTime hSpace hSpace2 hSmoothTime
    hSmoothSpace hJoint K hK hBound Xeps XepsLeft X2 hXepsInitial hXepsLeft
    hX2Representation hXepsRepresentation Mε hMRepresentation hConv M e he he0 hA hSq hU
  have ha := Kyprianou.Ch04.actualRetainedFiniteAtomsAEV1 P triplet.levyMeasure
    triplet.levyMeasure_isLevyMeasure N X Xleft hLevy hLeft hNLaw (1/2) (by norm_num)
  filter_upwards [hp,ha] with w hw ha'
  intro t
  obtain ⟨S,hs,hR⟩ := ha' t
  let Y := fun n s => XepsLeft (e n) s w
  let L := fun s => Xleft s w
  have h := Kyprianou.Ch04.pathTimeWeightDCTV1 Y L fSpace K t hw.2.2.1 hw.2.2.2.1
    hJoint.2.2.1 (fun s x hs => (hBound s x hs).2.2.1) (fun s hs _ => hw.2.2.2.2.2 s hs)
  have hJ := Kyprianou.Ch04.finiteAtomWeightLimitV1 (N.N w) t S
    (fun r => X r w - Xleft r w) (fun r hr => ⟨(hs r hr).1,(hs r hr).2.1⟩)
    hR Y L fSpace hJoint.2.2.1 (fun s hs _ => hw.2.2.2.2.2 s hs)
  exact (tendsto_const_nhds.mul h).add hJ
