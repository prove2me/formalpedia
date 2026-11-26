-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45JointCutoffMomentClosureV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:06:46.107087+00:00
-- url     : https://prove2.me/submissions/975d4fde-ca04-4254-9d5a-0e1ff70f2cf5

import Theorems.Thm_Kyprianou_Ch03_completedNaturalMeasurableAELimitV1
import Theorems.Thm_Kyprianou_Ch04_exercise45SuppliedCutoffMartingaleV1
import Theorems.Thm_Kyprianou_Ch04_exercise45WeightedCutoffSupCauchyV1
import Theorems.Thm_Kyprianou_Ch04_terminalCauchyFromCompactSupV1
import Theorems.Thm_Kyprianou_Ch04_fullCutoffTerminalL2ClosureV1
import Theorems.Thm_Kyprianou_Ch04_terminalL1FromL2CutoffV1
import Theorems.Thm_Kyprianou_Ch04_compactUniformRightLimitV1
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false
/-- Close the common cutoff limit in the completed filtration and terminal L2. -/
theorem solution : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (F :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) (X : ℝ≥0 → Ω → ℝ) (hLevy :
    ProbabilityTheory.IsLevyProcess X P) (triplet : ProbabilityTheory.LevyKhintchineTriple)
    [SigmaFinite triplet.levyMeasure] (hNoGaussian : triplet.gaussianVariance = 0) (hTriplet : ∀ (t
    : ℝ≥0) (xi : ℝ), charFun (P.map (X t)) xi = Complex.exp (((t : ℝ) : Complex) *
    Kyprianou.Ch01.levyTripleExponent triplet xi)) (hFiltration :
    Kyprianou.Ch03.IsCompletedNaturalFiltration P X F) (N : PoissonRandomMeasure.{0,0,0} P
    triplet.levyMeasure) (Xleft : ℝ≥0 → Ω → ℝ) (hLeft : ∀ᵐ omega : Ω ∂P, ∀ t : ℝ≥0, 0 < t → Tendsto
    (fun s : ℝ≥0 => X s omega) (nhdsWithin t (Iio t)) (nhds (Xleft t omega))) (hNLaw : ∀ᵐ omega : Ω
    ∂P, N.N omega = Kyprianou.Ch04.pathJumpMeasure X Xleft omega) (f fTime fSpace fSpace2 : ℝ → ℝ
    -> ℝ) (hTime : ∀ s x : ℝ, fTime s x = deriv (fun u : ℝ => f u x) s) (hSpace : ∀ s x : ℝ, fSpace
    s x = deriv (fun u : ℝ => f s u) x) (hSpace2 : ∀ s x : ℝ, fSpace2 s x = deriv (fun u : ℝ =>
    fSpace s u) x) (hSmoothTime : ∀ x : ℝ, ContDiff ℝ 1 (fun s => f s x)) (hSmoothSpace : ∀ s : ℝ,
    ContDiff ℝ 2 (fun x => f s x)) (hJoint : ContinuousOn (fun z : ℝ × ℝ => f z.1 z.2) (Ici (0 : ℝ)
    ×ˢ univ) ∧ ContinuousOn (fun z : ℝ × ℝ => fTime z.1 z.2) (Ici (0 : ℝ) ×ˢ univ) ∧ ContinuousOn
    (fun z : ℝ × ℝ => fSpace z.1 z.2) (Ici (0 : ℝ) ×ˢ univ) ∧ ContinuousOn (fun z : ℝ × ℝ =>
    fSpace2 z.1 z.2) (Ici (0 : ℝ) ×ˢ univ)) (K : ℝ) (hK : 0 < K) (hBound : ∀ s x : ℝ, 0 ≤ s → |f s
    x| ≤ K ∧ |fTime s x| ≤ K ∧ |fSpace s x| ≤ K ∧ |fSpace2 s x| ≤ K) (Xeps : ℝ → ℝ≥0 → Ω → ℝ)
    (XepsLeft : ℝ → ℝ≥0 → Ω → ℝ) (X2 : ℝ≥0 → Ω → ℝ) (hXepsInitial : ∀ epsilon omega, 0 < epsilon →
    epsilon < 1 → Xeps epsilon 0 omega = X 0 omega) (hXepsLeft : ∀ epsilon : ℝ, 0 < epsilon →
    epsilon < 1 → ∀ᵐ omega : Ω ∂P, ∀ t : ℝ≥0, 0 < t → Tendsto (fun s : ℝ≥0 => Xeps epsilon s omega)
    (nhdsWithin t (Iio t)) (nhds (XepsLeft epsilon t omega))) (hX2Representation : ∀ t omega, X2 t
    omega = triplet.drift * (t : ℝ) + ∫ z in Set.prod (Icc (0 : ℝ) (t : ℝ)) {x : ℝ | 1 ≤ |x|}, z.2
    ∂(N.N omega)) (hXepsRepresentation : ∀ (epsilon : ℝ), 0 < epsilon → epsilon < 1 → ∀ t omega,
    Xeps epsilon t omega = X2 t omega + (∫ z in Set.prod (Icc (0 : ℝ) (t : ℝ)) {x : ℝ | epsilon <
    |x| ∧ |x| < 1}, z.2 ∂(N.N omega)) - (t : ℝ) * (∫ x in {x : ℝ | epsilon < |x| ∧ |x| < 1}, x
    ∂triplet.levyMeasure)) (Mε : ℝ → ℝ≥0 → Ω → ℝ) (hMRepresentation : ∀ (epsilon : ℝ), 0 < epsilon
    → epsilon < 1 → ∀ t omega, Mε epsilon t omega = (∫ z in Set.prod (Icc (0 : ℝ) (t : ℝ)) {x : ℝ |
    epsilon < |x| ∧ |x| < 1}, z.2 * fSpace z.1 (XepsLeft epsilon (Real.toNNReal z.1) omega) ∂(N.N
    omega)) - (∫ s in Icc (0 : ℝ) (t : ℝ), (∫ x in {x : ℝ | epsilon < |x| ∧ |x| < 1}, x * fSpace s
    (XepsLeft epsilon (Real.toNNReal s) omega) ∂triplet.levyMeasure) ∂volume)), (∀ᵐ omega : Ω ∂P, ∀
    t : ℝ≥0, Tendsto (fun epsilon : ℝ => Xeps epsilon t omega) (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds
    (X t omega))) → ∀ (M : ℝ≥0 → Ω → ℝ) (e : ℕ → ℝ), (∀ n, 0 < e n ∧ e n < 1) → Tendsto e atTop
    (nhds 0) → (∀ᵐ w ∂P, ∀ T : ℝ≥0, ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ t : ℝ≥0, t ≤ T → |Xeps
    (e n) t w - X t w| < δ ∧ |Mε (e n) t w - M t w| < δ) → StronglyAdapted F M ∧ (∀ t : ℝ≥0,
    Integrable (M t) P) ∧ (∀ t : ℝ≥0, Tendsto (fun n => ∫ w, |Mε (e n) t w - M t w| ∂P) atTop (nhds
    0)) ∧ (∀ t : ℝ≥0, Integrable (fun omega : Ω => (M t omega)^2) P) ∧ (∀ᵐ omega : Ω ∂P, ∀ t : ℝ≥0,
    Tendsto (fun s : ℝ≥0 => M s omega) (nhdsWithin t (Ioi t)) (nhds (M t omega))) ∧ (∀ t : ℝ≥0,
    Tendsto (fun epsilon : ℝ => (∫ omega, (Mε epsilon t omega - M t omega)^2 ∂P)) (nhdsWithin (0 :
    ℝ) (Ioi 0)) (nhds 0)) := by
  intro Ω m P hP F X hLevy triplet hSigma hNoGaussian hTriplet hFiltration N
    Xleft hLeft hNLaw f fTime fSpace fSpace2 hTime hSpace hSpace2 hSmoothTime
    hSmoothSpace hJoint K hK hBound Xeps XepsLeft X2 hXepsInitial hXepsLeft
    hX2Representation hXepsRepresentation Mε hMRepresentation hConv M e he he0 hU
  have hm := Kyprianou.Ch04.exercise45SuppliedCutoffMartingaleV1 P F X hLevy triplet
    hNoGaussian hTriplet hFiltration N Xleft hLeft hNLaw f fTime fSpace fSpace2
    hTime hSpace hSpace2 hSmoothTime hSmoothSpace hJoint K hK hBound
    Xeps XepsLeft X2 hXepsInitial hXepsLeft hX2Representation hXepsRepresentation
    Mε hMRepresentation hConv
  have hc := Kyprianou.Ch04.exercise45WeightedCutoffSupCauchyV1 P F X hLevy triplet
    hNoGaussian hTriplet hFiltration N Xleft hLeft hNLaw f fTime fSpace fSpace2
    hTime hSpace hSpace2 hSmoothTime hSmoothSpace hJoint K hK hBound
    Xeps XepsLeft X2 hXepsInitial hXepsLeft hX2Representation hXepsRepresentation
    Mε hMRepresentation hConv
  have hY (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (t : NNReal) :=
    ((hm a ha ha1).1.stronglyAdapted t).mono (F.le t)
  have hl (t : NNReal) : ∀ᵐ w ∂P, Tendsto (fun n => Mε (e n) t w) atTop (nhds (M t w)) := by
    filter_upwards [hU] with w hw
    apply Metric.tendsto_nhds.mpr
    intro δ hd
    obtain ⟨J,hJ⟩ := hw t δ hd
    exact eventually_atTop.mpr ⟨J,fun n hn => by
      simpa [Real.dist_eq] using (hJ n hn t le_rfl).2⟩
  have hA : StronglyAdapted F M := fun t =>
    (Kyprianou.Ch03.completedNaturalMeasurableAELimitV1 P X F hFiltration t
      (fun n => Mε (e n) t) (M t)
      (fun n => ((hm (e n) (he n).1 (he n).2).1.stronglyAdapted t).measurable)
      (hl t)).stronglyMeasurable
  have hC := Kyprianou.Ch04.terminalCauchyFromCompactSupV1 P Mε
    (fun a ha ha1 t => ⟨(hY a ha ha1 t).measurable,(hm a ha ha1).2.1 t⟩) hc
  have hL2 (t : NNReal) := Kyprianou.Ch04.fullCutoffTerminalL2ClosureV1 P
    (fun a => Mε a t) (M t) e he he0 (fun a ha ha1 => (hY a ha ha1 t).measurable)
    (fun a ha ha1 => (hm a ha ha1).2.1 t) ((hA t).mono (F.le t)).measurable (hl t) (hC t)
  have heP : Tendsto e atTop (nhdsWithin 0 (Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨he0,Eventually.of_forall fun n => (he n).1⟩
  have hL1 (t : NNReal) := Kyprianou.Ch04.terminalL1FromL2CutoffV1 P
    (fun n => Mε (e n) t) (M t) (fun n => (hY (e n) (he n).1 (he n).2 t).measurable)
    ((hA t).mono (F.le t)).measurable (fun n => (hm (e n) (he n).1 (he n).2).2.1 t)
    (hL2 t).1 ((hL2 t).2.comp heP)
  have hr : ∀ᵐ w ∂P, ∀ n t, Tendsto (fun s => Mε (e n) s w)
      (nhdsWithin t (Ioi t)) (nhds (Mε (e n) t w)) :=
    ae_all_iff.mpr fun n => (hm (e n) (he n).1 (he n).2).2.2
  refine ⟨hA,fun t => (hL1 t).1,fun t => (hL1 t).2,fun t => (hL2 t).1,?_,
    fun t => (hL2 t).2⟩
  filter_upwards [hr,hU] with w hw hu
  exact Kyprianou.Ch04.compactUniformRightLimitV1 (fun n t => Mε (e n) t w) (fun t => M t w)
    hw (fun T δ hd => by
      obtain ⟨J,hJ⟩ := hu T δ hd
      exact ⟨J,fun n hn t ht => (hJ n hn t ht).2⟩)
