-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45PhysicalItoFromUniformV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:27:03.470791+00:00
-- url     : https://prove2.me/submissions/b4cdc8ab-01cb-4119-a536-c44bc7749b74

import Theorems.Thm_Kyprianou_Ch04_exercise45PhysicalFiniteCutoffItoV1
import Theorems.Thm_Kyprianou_Ch04_exercise45ItoTimeLimitV1
import Theorems.Thm_Kyprianou_Ch04_exercise45ItoJumpLimitV1
import Theorems.Thm_Kyprianou_Ch04_exercise45ItoLargeIntegralLimitV1
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false
/-- Pass the finite cutoff identity through the three physical integral limits. -/
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
        ∧ |Mε (e n) t w - M t w| < δ) → (∀ᵐ omega : Ω ∂P, ∀ t : ℝ≥0, f (t : ℝ) (X t omega) = f 0
        (X 0 omega) + (∫ s in Icc (0 : ℝ) (t : ℝ), fTime s (X (Real.toNNReal s) omega) ∂volume) +
        (∫ z in Set.prod (Icc (0 : ℝ) (t : ℝ)) univ, (f z.1 (Xleft (Real.toNNReal z.1) omega +
        z.2) - f z.1 (Xleft (Real.toNNReal z.1) omega) - z.2 * fSpace z.1 (Xleft (Real.toNNReal
        z.1) omega)) ∂(N.N omega)) + x2Integral t omega + M t omega) := by
  intro Ω m P hP F X hLevy triplet hSigma hNoGaussian hTriplet hFiltration N
    Xleft hLeft hNLaw f fTime fSpace fSpace2 hTime hSpace hSpace2 hSmoothTime
    hSmoothSpace hJoint K hK hBound Xeps XepsLeft X2 hXepsInitial hXepsLeft
    hX2Representation hXepsRepresentation Mε hMRepresentation hConv I2 M e he he0 hA hSq hU
  have htime := Kyprianou.Ch04.exercise45ItoTimeLimitV1 P F X hLevy triplet
    hNoGaussian hTriplet hFiltration N Xleft hLeft hNLaw f fTime fSpace fSpace2
    hTime hSpace hSpace2 hSmoothTime hSmoothSpace hJoint K hK hBound
    Xeps XepsLeft X2 hXepsInitial hXepsLeft hX2Representation hXepsRepresentation
    Mε hMRepresentation hConv M e he he0 hA hSq hU
  have hjump := Kyprianou.Ch04.exercise45ItoJumpLimitV1 P F X hLevy triplet
    hNoGaussian hTriplet hFiltration N Xleft hLeft hNLaw f fTime fSpace fSpace2
    hTime hSpace hSpace2 hSmoothTime hSmoothSpace hJoint K hK hBound
    Xeps XepsLeft X2 hXepsInitial hXepsLeft hX2Representation hXepsRepresentation
    Mε hMRepresentation hConv M e he he0 hA hSq hU
  have hlarge := Kyprianou.Ch04.exercise45ItoLargeIntegralLimitV1 P F X hLevy triplet
    hNoGaussian hTriplet hFiltration N Xleft hLeft hNLaw f fTime fSpace fSpace2
    hTime hSpace hSpace2 hSmoothTime hSmoothSpace hJoint K hK hBound
    Xeps XepsLeft X2 hXepsInitial hXepsLeft hX2Representation hXepsRepresentation
    Mε hMRepresentation hConv M e he he0 hA hSq hU
  have hfinite := ae_all_iff.mpr (fun n : ℕ =>
    Kyprianou.Ch04.exercise45PhysicalFiniteCutoffItoV1 P F X hLevy triplet
    hNoGaussian hTriplet hFiltration N Xleft hLeft hNLaw f fTime fSpace fSpace2
    hTime hSpace hSpace2 hSmoothTime hSmoothSpace hJoint K hK hBound
    Xeps XepsLeft X2 hXepsInitial hXepsLeft hX2Representation hXepsRepresentation (e n) (he n).1 (he n).2)
  filter_upwards [hfinite,htime,hjump,hlarge,hU] with w hw ht hj hl hu
  intro t
  have hconv' : Tendsto (fun n => Xeps (e n) t w) atTop (nhds (X t w)) ∧
      Tendsto (fun n => Mε (e n) t w) atTop (nhds (M t w)) := by
    constructor <;> apply Metric.tendsto_nhds.mpr <;> intro δ hd <;>
      obtain ⟨J,hJ⟩ := hu t δ hd
    · exact eventually_atTop.mpr ⟨J,fun n hn => by
        simpa [Real.dist_eq] using (hJ n hn t le_rfl).1⟩
    · exact eventually_atTop.mpr ⟨J,fun n hn => by
        simpa [Real.dist_eq] using (hJ n hn t le_rfl).2⟩
  have hpair : Tendsto (fun n => ((t : ℝ),Xeps (e n) t w)) atTop
      (nhdsWithin ((t : ℝ),X t w) (Ici (0 : ℝ) ×ˢ univ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_const_nhds.prodMk_nhds hconv'.1,
      Eventually.of_forall fun _ => ⟨t.coe_nonneg,mem_univ _⟩⟩
  have hf := (hJoint.1 ((t : ℝ),X t w) ⟨t.coe_nonneg,mem_univ _⟩).tendsto.comp hpair
  have hR := (((tendsto_const_nhds (x := f 0 (X 0 w))).add (ht t)).add
    (hj t)).add (hl t) |>.add hconv'.2
  apply tendsto_nhds_unique hf
  apply hR.congr'
  filter_upwards [] with n
  have h := (hw n t).symm
  rw [← hMRepresentation (e n) (he n).1 (he n).2 t w] at h
  exact h
