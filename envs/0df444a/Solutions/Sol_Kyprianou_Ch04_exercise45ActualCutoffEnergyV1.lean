-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45ActualCutoffEnergyV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:39:36.448323+00:00
-- url     : https://prove2.me/submissions/9659bd2d-30d4-451b-bc15-403b1e632f81
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch04_exercise45ActualCutoffRawEnergyV1
import Theorems.Thm_Kyprianou_Ch04_actualCutoffMaximalBoundV1
import Theorems.Thm_Kyprianou_Ch04_affineLeftLimitBudgetV1
import Theorems.Thm_Kyprianou_Ch04_weightedCutoffIntegratedBudgetV1
import Theorems.Thm_Kyprianou_Ch04_actualCutoffAffineStepsV1
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
/-- Exercise 4.5(ii) terminal energy from the actual isometry and left-limit budget. -/
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
    ∂triplet.levyMeasure) ∂volume)) ∧ MeasureTheory.Martingale (M epsilon) F P) -> ∀ a b : ℝ, 0
    < a → a ≤ b → b < 1 → (∫ ω, (M a T ω - M b T ω)^2 ∂P) ≤ (K^2 * (T : ℝ) * (1 + 4 * (T : ℝ) *
    (∫⁻ z in {z : ℝ | |z| < 1}, ENNReal.ofReal (z^2) ∂triplet.levyMeasure).toReal)) * (∫⁻ z in
    {z : ℝ | |z| ≤ b}, ENNReal.ofReal (z^2) ∂triplet.levyMeasure).toReal := by
  intro Ω m P hP F X hLevy triplet hSigma hNoGaussian hTriplet hFiltration N
    Xleft hLeft hNLaw f fTime fSpace fSpace2 hTime hSpace hSpace2 hSmoothTime
    hSmoothSpace hJoint K hK hBound Xeps XepsLeft X2 hXepsInitial hXepsLeft
    hX2Representation hXepsRepresentation T hT M hM a b ha hab hb
  rcases hab.eq_or_lt with rfl | hab
  · simp <;> positivity
  let ν := triplet.levyMeasure
  have hν := triplet.levyMeasure_isLevyMeasure
  have ha1 := hab.trans hb
  have hb0 := ha.trans hab
  have hRaw := Kyprianou.Ch04.exercise45ActualCutoffRawEnergyV1 P F X hLevy
    triplet hNoGaussian hTriplet hFiltration N Xleft hLeft hNLaw f fTime fSpace fSpace2
    hTime hSpace hSpace2 hSmoothTime hSmoothSpace hJoint K hK hBound Xeps XepsLeft X2
    hXepsInitial hXepsLeft hX2Representation hXepsRepresentation T hT M hM a b ha hab hb
  let S (ω : Ω) := sSup ((fun t : NNReal => |Xeps a t ω - Xeps b t ω|^2) '' Iic T)
  have hMax := Kyprianou.Ch04.actualCutoffMaximalBoundV1 P ν hν N X Xleft X2
    (Xeps a) (Xeps b) a b ha hab hb hNLaw (hXepsRepresentation a ha ha1)
    (hXepsRepresentation b hb0 hb) T hT
  have hAff (e : ℝ) (he : 0 < e) (he1 : e < 1) : ∀ᵐ ω ∂P, ∀ n : ℕ,
      ∃ (L S : Finset (ℝ × ℝ)) (a c : ℝ × ℝ → ℝ), ∀ t : NNReal, t ≤ (n : NNReal) →
        Xeps e t ω = (triplet.drift - ∫ x in {x : ℝ | e < |x| ∧ |x| < 1}, x ∂ν) * (t : ℝ) +
          (∑ p ∈ L, if p.1 ≤ (t : ℝ) then a p else 0) +
          (∑ p ∈ S, if p.1 ≤ (t : ℝ) then c p else 0) := by
    filter_upwards [Kyprianou.Ch04.actualCutoffAffineStepsV1 P ν hν N X Xleft X2 (Xeps e)
      triplet.drift e he hNLaw hX2Representation (hXepsRepresentation e he he1)] with ω hω
    intro n
    obtain ⟨L,S,a,c,h⟩ := hω n
    exact ⟨L,S,a,c,fun t ht => (h t ht).2⟩
  have hLeftBudget := Kyprianou.Ch04.affineLeftLimitBudgetV1 P (Xeps a) (Xeps b)
    (XepsLeft a) (XepsLeft b) _ _ T (hAff a ha ha1) (hAff b hb0 hb)
    (hXepsLeft a ha ha1) (hXepsLeft b hb0 hb)
  have hG (s : ℝ) (_ : 0 ≤ s) : Differentiable ℝ (fSpace s) := by
    have hf : fSpace s = deriv (f s) := funext (hSpace s)
    rw [hf]
    exact (hSmoothSpace s).differentiable_deriv_two
  exact hRaw.trans (Kyprianou.Ch04.weightedCutoffIntegratedBudgetV1 P ν hν a b K ha hab hb hK.le
    T fSpace (XepsLeft a) (XepsLeft b) S hG (fun s x hs => (hBound s x hs).2.2.1)
    (fun s x hs => by rw [← hSpace2]; exact (hBound s x hs).2.2.2)
    hMax.1 (hLeftBudget.mono fun ω h => h.1) (hLeftBudget.mono fun ω h => h.2) hMax.2)
