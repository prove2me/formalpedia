-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45LocalisedPhysicalDataV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:37:51.849559+00:00
-- url     : https://prove2.me/submissions/6506f85b-c1f8-46ea-9217-fe46e2e3009e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch04_exercise45SmoothTestCutoffV1
import Theorems.Thm_Kyprianou_Ch04_exercise45BoundedPhysicalWitnessV2
import Theorems.Thm_Kyprianou_Ch04_exercise45PhysicalPrefixAgreementV1
import Theorems.Thm_Kyprianou_Ch04_exercise45LocalisedFamilyAssemblyV1
import Theorems.Thm_Kyprianou_Ch04_exercise45FiniteCofinalStopsV1
import Theorems.Thm_Kyprianou_Ch04_exercise45RightContinuousStoppedMartingaleV1
import Theorems.Thm_Kyprianou_Ch03_completedNaturalLevyFiltrationRightContinuous
import Theorems.Thm_Kyprianou_Ch03_completedNaturalCoordinateAdaptedV1
import Theorems.Thm_Kyprianou_Ch04_rightContinuousTimeMeasurableV1
import Theorems.Thm_Kyprianou_Ch04_leftLimitTimeMeasurableV1
import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open Kyprianou.Ch04 MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false

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
  omega))) (hLeftZero : ∀ᵐ w ∂P, Xleft 0 w = X 0 w) (hNLaw : ∀ᵐ omega : Omega ∂P, N.N omega =
  Kyprianou.Ch04.pathJumpMeasure X Xleft omega) (f fTime fSpace fSpace2 : Real -> Real -> Real)
  (hTime : ∀ s x : Real, fTime s x = deriv (fun u : Real => f u x) s) (hSpace : ∀ s x : Real,
  fSpace s x = deriv (fun u : Real => f s u) x) (hSpace2 : ∀ s x : Real, fSpace2 s x = deriv (fun
  u : Real => fSpace s u) x) (hSmoothTime : ∀ x : Real, ContDiff Real 1 (fun s => f s x))
  (hSmoothSpace : ∀ s : Real, ContDiff Real 2 (fun x => f s x)) (hJoint : ContinuousOn (fun z :
  Real × Real => f z.1 z.2) (Set.Ici (0 : Real) ×ˢ Set.univ) ∧ ContinuousOn (fun z : Real × Real
  => fTime z.1 z.2) (Set.Ici (0 : Real) ×ˢ Set.univ) ∧ ContinuousOn (fun z : Real × Real => fSpace
  z.1 z.2) (Set.Ici (0 : Real) ×ˢ Set.univ) ∧ ContinuousOn (fun z : Real × Real => fSpace2 z.1
  z.2) (Set.Ici (0 : Real) ×ˢ Set.univ)) (X2 : NNReal -> Omega -> Real) (hX2Representation : ∀ t
  omega, X2 t omega = triplet.drift * (t : Real) + ∫ z in Set.prod (Set.Icc (0 : Real) (t : Real))
  {x : Real | 1 ≤ |x|}, z.2 ∂(N.N omega)),
    let H (a : ℝ → ℝ → ℝ) : NNReal → Omega → ℝ := fun t w => a (t : ℝ) (Xleft t w)
    let D (a : ℝ → ℝ → ℝ) : NNReal → Omega → ℝ := fun t w =>
      triplet.drift * (∫ s in Icc (0 : ℝ) (t : ℝ), a s (Xleft s.toNNReal w)) +
        ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|},
          z.2 * a z.1 (Xleft z.1.toNNReal w) ∂(N.N w)
    let R (a atime ax : ℝ → ℝ → ℝ) : NNReal → Omega → ℝ := fun t w =>
      a (t : ℝ) (X t w) - (a 0 (X 0 w) +
        (∫ s in Icc (0 : ℝ) (t : ℝ), atime s (X s.toNNReal w) ∂volume) +
        (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ univ,
          (a z.1 (Xleft z.1.toNNReal w + z.2) - a z.1 (Xleft z.1.toNNReal w) -
            z.2 * ax z.1 (Xleft z.1.toNNReal w)) ∂(N.N w)))
    ∃ (Hn Dn Rn Mn : ℕ → NNReal → Omega → ℝ) (τ : ℕ → Omega → NNReal),
      (∀ n t, MeasurableSet[F t] {w | τ n w ≤ t}) ∧
      (∀ w, Monotone (fun n => τ n w)) ∧
      (∀ᵐ w ∂P, Tendsto (fun n => (τ n w : WithTop NNReal)) atTop (nhds ⊤)) ∧
      (∀ᵐ w ∂P, ∀ n t, t ≤ τ n w → Hn n t w = H fSpace t w ∧ Dn n t w = D fSpace t w) ∧
      (∀ᵐ w ∂P, ∀ n t, t < τ n w → Rn n t w = R f fTime fSpace t w) ∧
      (∀ n, IsStochasticIntegralInProbabilityV2 P X (Hn n) (fun t w => Dn n t w + Mn n t w)) ∧
      (∀ n, ∀ᵐ w ∂P, ∀ t, Rn n t w = Dn n t w + Mn n t w) ∧
      (∀ n, Martingale (fun t w => Mn n (min t (τ n w)) w) F P) := by
  intro Ω m P hP F X hLevy triplet hSigma hNoGaussian hTriplet hFiltration N
    Xleft hLeft hLeftZero hNLaw f fTime fSpace fSpace2 hTime hSpace hSpace2
    hSmoothTime hSmoothSpace hJoint X2 hX2Representation
  intro H D R
  have hRC := Kyprianou.Ch03.completedNaturalLevyFiltrationRightContinuous P X hLevy F hFiltration
  have hNull (s : NNReal) (N₀ A : Set Ω) (hN₀ : MeasurableSet N₀)
      (hzero : P N₀ = 0) (hsub : A ⊆ N₀) : MeasurableSet[F s] A := by
    rw [hFiltration s]
    apply (le_sup_right : MeasurableSpace.generateFrom _ ≤ _)
    exact MeasurableSpace.measurableSet_generateFrom ⟨N₀,hN₀,hzero,hsub⟩
  obtain ⟨τ,hτ,hStop,hMono,hCof,hBounds⟩ := exercise45FiniteCofinalStopsV1 P F X Xleft
    hLevy hRC hNull (Kyprianou.Ch03.completedNaturalCoordinateAdaptedV1 P X F hFiltration)
    hLeft hLeftZero
  choose g gt gx gxx K hg using fun n : ℕ => exercise45SmoothTestCutoffV1
    f fTime fSpace fSpace2 hTime hSpace hSpace2 hSmoothTime hSmoothSpace hJoint n
  have hW (n : ℕ) : ∃ M : NNReal → Ω → ℝ, Martingale M F P ∧
      (∀ᵐ w ∂P, ∀ t, ContinuousWithinAt (fun u => M u w) (Ici t) t) ∧
      IsStochasticIntegralInProbabilityV2 P X (H (gx n)) (fun t w => D (gx n) t w + M t w) ∧
      (∀ᵐ w ∂P, ∀ t, R (g n) (gt n) (gx n) t w = D (gx n) t w + M t w) := by
    obtain ⟨hK,hT,hS,hS2,hST,hSS,hJ,hB,hEq⟩ := hg n
    exact exercise45BoundedPhysicalWitnessV2 P F X hLevy triplet hNoGaussian hTriplet
      hFiltration N Xleft hLeft hLeftZero hNLaw (g n) (gt n) (gx n) (gxx n)
      hT hS hS2 hST hSS hJ X2 hX2Representation (K n) hK hB
  choose M hM using hW
  have hpath : ∀ᵐ w ∂P, ∀ n,
      (∀ t ≤ τ n w, H (gx n) t w = H fSpace t w ∧ D (gx n) t w = D fSpace t w) ∧
      (∀ t < τ n w, R (g n) (gt n) (gx n) t w = R f fTime fSpace t w) := by
    filter_upwards [hBounds,hLevy.cadlag_ae,hLeft,hNLaw] with w hb hc hl hn
    intro n
    have hx := rightContinuousTimeMeasurableV1 (fun t => X t w) (fun t => (hc t).1)
    have hleft := leftLimitTimeMeasurableV1 (fun t => X t w) (fun t => Xleft t w) hx hl
    obtain ⟨_,_,_,_,_,_,_,_,he⟩ := hg n
    simpa only [H,D,R,hn] using exercise45PhysicalPrefixAgreementV1 X Xleft w triplet.drift
      f fTime fSpace (g n) (gt n) (gx n) n (τ n w) (hτ n w) hx hleft
      (hb n).1 (hb n).2 (fun s x hs hsn hx => ⟨(he s x hs hsn hx).1,
        (he s x hs hsn hx).2.1,(he s x hs hsn hx).2.2.1⟩)
  have hp : ∀ᵐ w ∂P, ∀ n t, t ≤ τ n w →
      H (gx n) t w = H fSpace t w ∧ D (gx n) t w = D fSpace t w :=
    hpath.mono fun w hw n => (hw n).1
  have hr : ∀ᵐ w ∂P, ∀ n t, t < τ n w →
      R (g n) (gt n) (gx n) t w = R f fTime fSpace t w :=
    hpath.mono fun w hw n => (hw n).2
  have hm (n : ℕ) (t : NNReal) : MeasurableSet[F t] {w | τ n w ≤ t} := by
    simpa only [WithTop.coe_le_coe] using hStop n t

  refine ⟨fun n => H (gx n),fun n => D (gx n),fun n => R (g n) (gt n) (gx n),M,τ,
    hm,hMono,hCof,hp,hr,(fun n => (hM n).2.2.1),(fun n => (hM n).2.2.2),?_⟩
  intro n
  exact exercise45RightContinuousStoppedMartingaleV1 P F hRC hNull (M n)
    (hM n).1 (hM n).2.1 (τ n) (hStop n)
