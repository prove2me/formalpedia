-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45PhysicalUCPFromUniformV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:29:34.92329+00:00
-- url     : https://prove2.me/submissions/67568e3c-0a4e-41bd-87f0-47ba2150179f

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise45FixedCutoffGridUCPV4
import Theorems.Thm_Kyprianou_Ch04_exercise45UniformCutoffGridErrorV4
import Theorems.Thm_Kyprianou_Ch04_ito43_ucp_approximation
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false

/-- Combine finite-cutoff UCP with a uniform error bound. -/
theorem solution :
∀ {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P] (F :
Filtration NNReal (inferInstance : MeasurableSpace Omega)) (X : NNReal -> Omega -> Real) (hLevy
: ProbabilityTheory.IsLevyProcess X P) (triplet : ProbabilityTheory.LevyKhintchineTriple)
[SigmaFinite triplet.levyMeasure] (hNoGaussian : triplet.gaussianVariance = 0) (hTriplet : ∀ (t
: NNReal) (xi : Real), charFun (P.map (X t)) xi = Complex.exp (((t : Real) : Complex) *
Kyprianou.Ch01.levyTripleExponent triplet xi)) (hFiltration :
Kyprianou.Ch03.IsCompletedNaturalFiltration P X F) (N : PoissonRandomMeasure.{0,0,0} P
triplet.levyMeasure) (Xleft : NNReal -> Omega -> Real) (hLeft : ∀ᵐ omega : Omega ∂P, ∀ t :
NNReal, 0 < t -> Tendsto (fun s : NNReal => X s omega) (nhdsWithin t (Set.Iio t)) (nhds (Xleft t
omega))) (hNLaw : ∀ᵐ omega : Omega ∂P, N.N omega = Kyprianou.Ch04.pathJumpMeasure X Xleft omega)
(f fTime fSpace fSpace2 : Real -> Real -> Real) (hTime : ∀ s x : Real, fTime s x = deriv (fun u
: Real => f u x) s) (hSpace : ∀ s x : Real, fSpace s x = deriv (fun u : Real => f s u) x)
(hSpace2 : ∀ s x : Real, fSpace2 s x = deriv (fun u : Real => fSpace s u) x) (hSmoothTime : ∀ x
: Real, ContDiff Real 1 (fun s => f s x)) (hSmoothSpace : ∀ s : Real, ContDiff Real 2 (fun x =>
f s x)) (hJoint : ContinuousOn (fun z : Real × Real => f z.1 z.2) (Set.Ici (0 : Real) ×ˢ
Set.univ) ∧ ContinuousOn (fun z : Real × Real => fTime z.1 z.2) (Set.Ici (0 : Real) ×ˢ Set.univ)
∧ ContinuousOn (fun z : Real × Real => fSpace z.1 z.2) (Set.Ici (0 : Real) ×ˢ Set.univ) ∧
ContinuousOn (fun z : Real × Real => fSpace2 z.1 z.2) (Set.Ici (0 : Real) ×ˢ Set.univ)) (K :
Real) (hK : 0 < K) (hBound : ∀ s x : Real, 0 ≤ s -> |f s x| ≤ K ∧ |fTime s x| ≤ K ∧ |fSpace s x|
≤ K ∧ |fSpace2 s x| ≤ K) (Xeps : Real -> NNReal -> Omega -> Real) (XepsLeft : Real -> NNReal ->
Omega -> Real) (X2 : NNReal -> Omega -> Real) (hXepsInitial : ∀ epsilon omega, 0 < epsilon ->
epsilon < 1 -> Xeps epsilon 0 omega = X 0 omega) (hXepsLeft : ∀ epsilon : Real, 0 < epsilon ->
epsilon < 1 -> ∀ᵐ omega : Omega ∂P, ∀ t : NNReal, 0 < t -> Tendsto (fun s : NNReal => Xeps
epsilon s omega) (nhdsWithin t (Set.Iio t)) (nhds (XepsLeft epsilon t omega)))
(hX2Representation : ∀ t omega, X2 t omega = triplet.drift * (t : Real) + ∫ z in Set.prod
(Set.Icc (0 : Real) (t : Real)) {x : Real | 1 ≤ |x|}, z.2 ∂(N.N omega)) (hXepsRepresentation : ∀
(epsilon : Real), 0 < epsilon -> epsilon < 1 -> ∀ t omega, Xeps epsilon t omega = X2 t omega +
(∫ z in Set.prod (Set.Icc (0 : Real) (t : Real)) {x : Real | epsilon < |x| ∧ |x| < 1}, z.2 ∂(N.N
omega)) - (t : Real) * (∫ x in {x : Real | epsilon < |x| ∧ |x| < 1}, x ∂triplet.levyMeasure))
(Mε : Real -> NNReal -> Omega -> Real) (hMRepresentation : ∀ (epsilon : Real), 0 < epsilon ->
epsilon < 1 -> ∀ t omega, Mε epsilon t omega = (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real))
{x : Real | epsilon < |x| ∧ |x| < 1}, z.2 * fSpace z.1 (XepsLeft epsilon (Real.toNNReal z.1)
omega) ∂(N.N omega)) - (∫ s in Set.Icc (0 : Real) (t : Real), (∫ x in {x : Real | epsilon < |x|
∧ |x| < 1}, x * fSpace s (XepsLeft epsilon (Real.toNNReal s) omega) ∂triplet.levyMeasure)
∂volume)), (∀ᵐ omega : Omega ∂P, ∀ t : NNReal, Tendsto (fun epsilon : Real => Xeps epsilon t
omega) (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds (X t omega))) ->
      let x2Integral : NNReal → Omega → Real := fun t omega =>
        triplet.drift * (∫ s in Set.Icc (0 : Real) (t : Real), fSpace s (Xleft s.toNNReal omega)) +
        ∫ z in Set.Icc (0 : Real) (t : Real) ×ˢ {x : Real | 1 ≤ |x|},
          z.2 * fSpace z.1 (Xleft z.1.toNNReal omega) ∂(N.N omega)
      ∀ (M : NNReal → Omega → Real) (e : ℕ → ℝ),
          (∀ n, 0 < e n ∧ e n < 1) →
          Tendsto e atTop (nhds 0) →
          StronglyAdapted F M →
          (∀ t : NNReal, Integrable (fun w => (M t w)^2) P) →
          (∀ᵐ w ∂P, ∀ T : NNReal, ∀ δ : ℝ, 0 < δ →
            ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ t : NNReal, t ≤ T →
              |Xeps (e n) t w - X t w| < δ ∧ |Mε (e n) t w - M t w| < δ) →
          Kyprianou.Ch04.IsStochasticIntegralInProbabilityV2 P X
            (fun s omega => fSpace (s : Real) (Xleft s omega))
            (fun t omega => x2Integral t omega + M t omega) := by
  intro Ω m P hP F X hLevy triplet hSigma hNoGaussian hTriplet hFiltration N
    Xleft hLeft hNLaw f fTime fSpace fSpace2 hTime hSpace hSpace2 hSmoothTime
    hSmoothSpace hJoint K hK hBound Xeps XepsLeft X2 hXepsInitial hXepsLeft
    hX2Representation hXepsRepresentation Mε hMRepresentation hConv I2 M e he he0 hA hSq hU
  intro T δ hδ
  let G : (NNReal → Ω → ℝ) → (NNReal → Ω → ℝ) → ℕ → NNReal → Ω → ℝ :=
    fun Y H n t w => ∑ k ∈ Finset.range n,
      H (T * (k : NNReal) / (n : NNReal)) w *
        (Y (min t (T * ((k+1 : ℕ) : NNReal) / (n : NNReal))) w -
          Y (min t (T * (k : NNReal) / (n : NNReal))) w)
  let H : NNReal → Ω → ℝ := fun s w => fSpace (s : ℝ) (Xleft s w)
  let Hc : ℕ → NNReal → Ω → ℝ := fun m s w => fSpace (s : ℝ) (XepsLeft (e m) s w)
  let J : ℕ → NNReal → Ω → ℝ := fun m t w =>
    triplet.drift * (∫ s in Set.Icc (0 : ℝ) (t : ℝ), Hc m s.toNNReal w) +
    (∫ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|},
      z.2 * Hc m z.1.toNNReal w ∂(N.N w)) + Mε (e m) t w
  let E : ℕ → NNReal → Ω → ℝ := fun n t w => G X H n t w - (I2 t w + M t w)
  let A : ℕ → ℕ → NNReal → Ω → ℝ := fun m n t w =>
    G (Xeps (e m)) (Hc m) n t w - J m t w
  let B : ℕ → ℕ → NNReal → Ω → ℝ := fun m n t w => E n t w - A m n t w
  have hA' := Kyprianou.Ch04.exercise45FixedCutoffGridUCPV4 P F X hLevy triplet hNoGaussian hTriplet hFiltration N
    Xleft hLeft hNLaw f fTime fSpace fSpace2 hTime hSpace hSpace2 hSmoothTime
    hSmoothSpace hJoint K hK hBound Xeps XepsLeft X2 hXepsInitial hXepsLeft
    hX2Representation hXepsRepresentation Mε hMRepresentation hConv M e he he0 hA hSq hU T
  have hB' := Kyprianou.Ch04.exercise45UniformCutoffGridErrorV4 P F X hLevy triplet hNoGaussian hTriplet hFiltration N
    Xleft hLeft hNLaw f fTime fSpace fSpace2 hTime hSpace hSpace2 hSmoothTime
    hSmoothSpace hJoint K hK hBound Xeps XepsLeft X2 hXepsInitial hXepsLeft
    hX2Representation hXepsRepresentation Mε hMRepresentation hConv M e he he0 hA hSq hU T
  exact Kyprianou.Ch04.ito43_ucp_approximation P E A B T
    (fun m n t w => by dsimp [B]; ring) hA' hB' δ hδ
