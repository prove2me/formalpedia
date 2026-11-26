-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45ActualCutoffRightV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:57:13.333253+00:00
-- url     : https://prove2.me/submissions/39672c19-9f87-420a-9dd7-552215fd96cc

import Theorems.Thm_Kyprianou_Ch04_actualCutoffAffineStepsV1
import Theorems.Thm_Kyprianou_Ch04_affineLeftPathMeasurableV1
import Theorems.Thm_Kyprianou_Ch04_weightedRawIntegralRightV1
import Theorems.Thm_Kyprianou_Ch04_weightedCompensatorRightV1
import Theorems.Thm_Kyprianou_Ch04_pathJumpMeasureZeroTimeV1
import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
open MeasureTheory ProbabilityTheory Filter ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

open Set Topology

/-- Actual cutoff right continuity via the raw step integral and continuous compensator. -/
theorem solution
    : ∀ {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P] (F :
    Filtration NNReal (inferInstance : MeasurableSpace Omega)) (X : NNReal -> Omega -> Real)
    (hLevy : ProbabilityTheory.IsLevyProcess X P) (triplet :
    ProbabilityTheory.LevyKhintchineTriple) [SigmaFinite triplet.levyMeasure] (hNoGaussian :
    triplet.gaussianVariance = 0) (hTriplet : ∀ (t : NNReal) (xi : Real), charFun (P.map (X t))
    xi = Complex.exp (((t : Real) : Complex) * Kyprianou.Ch01.levyTripleExponent triplet xi))
    (hFiltration : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F) (N :
    PoissonRandomMeasure.{0,0,0} P triplet.levyMeasure) (Xleft : NNReal -> Omega -> Real) (hLeft
    : ∀ᵐ omega : Omega ∂P, ∀ t : NNReal, 0 < t -> Tendsto (fun s : NNReal => X s omega)
    (nhdsWithin t (Set.Iio t)) (nhds (Xleft t omega))) (hNLaw : ∀ᵐ omega : Omega ∂P, N.N omega =
    Kyprianou.Ch04.pathJumpMeasure X Xleft omega) (f fTime fSpace fSpace2 : Real -> Real ->
    Real) (hTime : ∀ s x : Real, fTime s x = deriv (fun u : Real => f u x) s) (hSpace : ∀ s x :
    Real, fSpace s x = deriv (fun u : Real => f s u) x) (hSpace2 : ∀ s x : Real, fSpace2 s x =
    deriv (fun u : Real => fSpace s u) x) (hSmoothTime : ∀ x : Real, ContDiff Real 1 (fun s => f
    s x)) (hSmoothSpace : ∀ s : Real, ContDiff Real 2 (fun x => f s x)) (hJoint : ContinuousOn
    (fun z : Real × Real => f z.1 z.2) (Set.Ici (0 : Real) ×ˢ Set.univ) ∧ ContinuousOn (fun z :
    Real × Real => fTime z.1 z.2) (Set.Ici (0 : Real) ×ˢ Set.univ) ∧ ContinuousOn (fun z : Real
    × Real => fSpace z.1 z.2) (Set.Ici (0 : Real) ×ˢ Set.univ) ∧ ContinuousOn (fun z : Real ×
    Real => fSpace2 z.1 z.2) (Set.Ici (0 : Real) ×ˢ Set.univ)) (K : Real) (hK : 0 < K) (hBound :
    ∀ s x : Real, 0 ≤ s -> |f s x| ≤ K ∧ |fTime s x| ≤ K ∧ |fSpace s x| ≤ K ∧ |fSpace2 s x| ≤ K)
    (Xeps : Real -> NNReal -> Omega -> Real) (XepsLeft : Real -> NNReal -> Omega -> Real) (X2 :
    NNReal -> Omega -> Real) (hXepsInitial : ∀ epsilon omega, 0 < epsilon -> epsilon < 1 -> Xeps
    epsilon 0 omega = X 0 omega) (hXepsLeft : ∀ epsilon : Real, 0 < epsilon -> epsilon < 1 -> ∀ᵐ
    omega : Omega ∂P, ∀ t : NNReal, 0 < t -> Tendsto (fun s : NNReal => Xeps epsilon s omega)
    (nhdsWithin t (Set.Iio t)) (nhds (XepsLeft epsilon t omega))) (hX2Representation : ∀ t
    omega, X2 t omega = triplet.drift * (t : Real) + ∫ z in Set.prod (Set.Icc (0 : Real) (t :
    Real)) {x : Real | 1 ≤ |x|}, z.2 ∂(N.N omega)) (hXepsRepresentation : ∀ (epsilon : Real), 0
    < epsilon -> epsilon < 1 -> ∀ t omega, Xeps epsilon t omega = X2 t omega + (∫ z in Set.prod
    (Set.Icc (0 : Real) (t : Real)) {x : Real | epsilon < |x| ∧ |x| < 1}, z.2 ∂(N.N omega)) - (t
    : Real) * (∫ x in {x : Real | epsilon < |x| ∧ |x| < 1}, x ∂triplet.levyMeasure)), ∀ (T :
    NNReal), 0 < T -> ∀ (M : Real -> NNReal -> Omega -> Real), (∀ epsilon : Real, 0 < epsilon ->
    epsilon < 1 -> (∀ t omega, M epsilon t omega = (∫ z in Set.prod (Set.Icc (0 : Real) (t :
    Real)) {x : Real | epsilon < |x| ∧ |x| < 1}, z.2 * fSpace z.1 (XepsLeft epsilon
    (Real.toNNReal z.1) omega) ∂(N.N omega)) - (∫ s in Set.Icc (0 : Real) (t : Real), (∫ x in {x
    : Real | epsilon < |x| ∧ |x| < 1}, x * fSpace s (XepsLeft epsilon (Real.toNNReal s) omega)
    ∂triplet.levyMeasure) ∂volume)) ∧ MeasureTheory.Martingale (M epsilon) F P) -> ∀ e : ℝ, 0 <
    e → e < 1 → ∀ᵐ ω ∂P, ∀ t : NNReal, Tendsto (fun s : NNReal => M e s ω) (nhdsWithin t
    (Set.Ioi t)) (nhds (M e t ω)) := by
  intro Ω m P hP F X hLevy triplet hSigma hNoGaussian hTriplet hFiltration N
    Xleft hLeft hNLaw f fTime fSpace fSpace2 hTime hSpace hSpace2 hSmoothTime
    hSmoothSpace hJoint K hK hBound Xeps XepsLeft X2 hXepsInitial hXepsLeft
    hX2Representation hXepsRepresentation T hT M hM e he he1
  let ν := triplet.levyMeasure
  have hν := triplet.levyMeasure_isLevyMeasure
  let B : Set ℝ := {z | e < |z| ∧ |z| < 1}
  have hB : MeasurableSet B :=
    (measurableSet_lt measurable_const measurable_id.abs).inter
      (measurableSet_lt measurable_id.abs measurable_const)
  have hfin : ν B < ⊤ :=
    (measure_mono (show B ⊆ {z | e ≤ |z|} from fun z hz => hz.1.le)).trans_lt
      (hν.measure_setOf_abs_ge_lt_top he)
  have hz : ∀ᵐ ω ∂P, N.N ω (({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ)) = 0 := by
    filter_upwards [hNLaw] with ω hω
    rw [hω]
    exact Kyprianou.Ch04.pathJumpMeasureZeroTimeV1 X Xleft ω
  have hRaw := Kyprianou.Ch04.weightedRawIntegralRightV1 P ν N B hB hfin
    (fun z ω => z.2 * fSpace z.1 (XepsLeft e z.1.toNNReal ω)) hz
  have hAffine := Kyprianou.Ch04.actualCutoffAffineStepsV1 P ν hν N X Xleft
    X2 (Xeps e) triplet.drift e he hNLaw hX2Representation (hXepsRepresentation e he he1)
  filter_upwards [hRaw,hAffine,hXepsLeft e he he1] with ω hR hA hL
  have hm : Measurable (fun t : NNReal => XepsLeft e t ω) := by
    apply Kyprianou.Ch04.affineLeftPathMeasurableV1
      (ι := (ℝ × ℝ) ⊕ (ℝ × ℝ)) (fun t => Xeps e t ω)
    · intro n
      obtain ⟨L,S,a,c,hLS⟩ := hA n
      refine ⟨L.disjSum S, Sum.elim Prod.fst Prod.fst, Sum.elim a c, 0,
        triplet.drift - ∫ x in B, x ∂ν, ?_⟩
      intro t ht
      simp only [Finset.sum_disjSum, Sum.elim_inl, Sum.elim_inr, zero_add, B, ← add_assoc]
      convert (hLS t ht).2 using 2
      · congr 1
      · apply Finset.sum_congr rfl
        intro p hp
        by_cases h : p.1 ≤ (t : ℝ) <;> simp [h]
    · exact hL
  have hc := Kyprianou.Ch04.weightedCompensatorRightV1 ν B
    (fun t => XepsLeft e t ω) hm fSpace K hK.le hJoint.2.2.1
    (fun s x hs => (hBound s x hs).2.2.1)
  intro t
  rw [(hM e he he1).1 t ω]
  exact ((hR t).sub (hc t)).congr (fun s => ((hM e he he1).1 s ω).symm)
