-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45ItoJumpLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:22:57.096932+00:00
-- url     : https://prove2.me/submissions/b728b6b0-b080-4917-b854-b5b377ba7d8f

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise45UniformCutoffPathRegularityV1
import Theorems.Thm_Kyprianou_Ch04_actualRetainedFiniteAtomsAEV1
import Theorems.Thm_Kyprianou_Ch04_exercise45MinSquareEnergyV2
import Theorems.Thm_Kyprianou_Ch04_pathJumpMeasureZeroTimeV1
import Theorems.Thm_Kyprianou_Ch04_exercise45TaylorBoundV2
import Theorems.Thm_Kyprianou_Ch04_exercise45PhysicalCorrectionLimitV3
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory ProbabilityTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical Topology
set_option autoImplicit false
/-- Physical cutoff limit from deterministic helper. -/
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
omega) (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds (X t omega))) -> ∀ (M : NNReal → Omega → Real) (e : ℕ → ℝ), (∀
n, 0 < e n ∧ e n < 1) → Tendsto e atTop (nhds 0) → StronglyAdapted F M → (∀ t : NNReal,
Integrable (fun w => (M t w)^2) P) → (∀ᵐ w ∂P, ∀ T : NNReal, ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n ≥
n₀, ∀ t : NNReal, t ≤ T → |Xeps (e n) t w - X t w| < δ ∧ |Mε (e n) t w - M t w| < δ) → ∀ᵐ w ∂P,
∀ t : NNReal, Tendsto (fun n => ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | e n < |x|}, (f z.1
(XepsLeft (e n) z.1.toNNReal w + z.2) - f z.1 (XepsLeft (e n) z.1.toNNReal w) - z.2 * fSpace z.1
(XepsLeft (e n) z.1.toNNReal w)) ∂(N.N w)) atTop (nhds (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ univ, (f
z.1 (Xleft z.1.toNNReal w + z.2) - f z.1 (Xleft z.1.toNNReal w) - z.2 * fSpace z.1 (Xleft
z.1.toNNReal w)) ∂(N.N w))) := by
  intro Ω m P hP F X hLevy triplet hSigma hNoGaussian hTriplet hFiltration N
    Xleft hLeft hNLaw f fTime fSpace fSpace2 hTime hSpace hSpace2 hSmoothTime
    hSmoothSpace hJoint K hK hBound Xeps XepsLeft X2 hXepsInitial hXepsLeft
    hX2Representation hXepsRepresentation Mε hMRepresentation hConv M e he he0 hA hSq hU
  have hp := Kyprianou.Ch04.exercise45UniformCutoffPathRegularityV1 P F X hLevy triplet hNoGaussian hTriplet hFiltration N
    Xleft hLeft hNLaw f fTime fSpace fSpace2 hTime hSpace hSpace2 hSmoothTime
    hSmoothSpace hJoint K hK hBound Xeps XepsLeft X2 hXepsInitial hXepsLeft
    hX2Representation hXepsRepresentation Mε hMRepresentation hConv M e he he0 hA hSq hU
  have hAtoms := Kyprianou.Ch04.actualRetainedFiniteAtomsAEV1 P triplet.levyMeasure
    triplet.levyMeasure_isLevyMeasure N X Xleft hLevy hLeft hNLaw (1/2) (by norm_num)
  have hEnergy := Kyprianou.Ch04.exercise45MinSquareEnergyV2 P triplet.levyMeasure
    triplet.levyMeasure_isLevyMeasure N
  filter_upwards [hp,hAtoms,hEnergy,hNLaw] with w hw hAt hEn hLaw
  intro t
  obtain ⟨S,hS,hR⟩ := hAt t
  have hz : N.N w ({0} ×ˢ (univ : Set ℝ)) = 0 := by
    rw [hLaw]
    exact Kyprianou.Ch04.pathJumpMeasureZeroTimeV1 X Xleft w
  exact Kyprianou.Ch04.exercise45PhysicalCorrectionLimitV3 (N.N w) t hz (hEn t)
    S (fun r => X r w-Xleft r w) hR f fSpace K hK.le hJoint.1 hJoint.2.2.1
    (fun s x z hs => (Kyprianou.Ch04.exercise45TaylorBoundV2 (f s) (fSpace s) (fSpace2 s)
      K hK.le (hSmoothSpace s) (hSpace s) (hSpace2 s)
      (fun x => (hBound s x hs).1) (fun x => (hBound s x hs).2.2.1)
      (fun x => (hBound s x hs).2.2.2) x z).2)
    (fun n u => XepsLeft (e n) u w) (fun u => Xleft u w) hw.2.2.1 hw.2.2.2.1
    hw.2.2.2.2.2 e he0
