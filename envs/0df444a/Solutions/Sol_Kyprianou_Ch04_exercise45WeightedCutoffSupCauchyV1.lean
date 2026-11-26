-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45WeightedCutoffSupCauchyV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:05:40.279522+00:00
-- url     : https://prove2.me/submissions/d806b0ba-d3fd-40aa-9761-e7b41c481e7c

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
import Theorems.Thm_Kyprianou_Ch04_exercise45SuppliedCutoffMartingaleV1
import Theorems.Thm_Kyprianou_Ch04_exercise_4_5_ii_goalV3
import Theorems.Thm_Kyprianou_Ch04_rightContinuousMartingaleCompactBddV1
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false
/-- Reuse the proved part ii Cauchy estimate and the compact bound for the difference of two actual right-continuous square-integrable martingales. -/
theorem solution : ∀ {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega)
    [IsProbabilityMeasure P] (F : Filtration NNReal (inferInstance : MeasurableSpace Omega)) (X :
    NNReal -> Omega -> Real) (hLevy : ProbabilityTheory.IsLevyProcess X P) (triplet :
    ProbabilityTheory.LevyKhintchineTriple) [SigmaFinite triplet.levyMeasure] (hNoGaussian :
    triplet.gaussianVariance = 0) (hTriplet : ∀ (t : NNReal) (xi : Real), charFun (P.map (X t)) xi
    = Complex.exp (((t : Real) : Complex) * Kyprianou.Ch01.levyTripleExponent triplet xi))
    (hFiltration : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F) (N :
    PoissonRandomMeasure.{0,0,0} P triplet.levyMeasure) (Xleft : NNReal -> Omega -> Real) (hLeft :
    ∀ᵐ omega : Omega ∂P, ∀ t : NNReal, 0 < t -> Tendsto (fun s : NNReal => X s omega) (nhdsWithin
    t (Set.Iio t)) (nhds (Xleft t omega))) (hNLaw : ∀ᵐ omega : Omega ∂P, N.N omega =
    Kyprianou.Ch04.pathJumpMeasure X Xleft omega) (f fTime fSpace fSpace2 : Real -> Real -> Real)
    (hTime : ∀ s x : Real, fTime s x = deriv (fun u : Real => f u x) s) (hSpace : ∀ s x : Real,
    fSpace s x = deriv (fun u : Real => f s u) x) (hSpace2 : ∀ s x : Real, fSpace2 s x = deriv
    (fun u : Real => fSpace s u) x) (hSmoothTime : ∀ x : Real, ContDiff Real 1 (fun s => f s x))
    (hSmoothSpace : ∀ s : Real, ContDiff Real 2 (fun x => f s x)) (hJoint : ContinuousOn (fun z :
    Real × Real => f z.1 z.2) (Set.Ici (0 : Real) ×ˢ Set.univ) ∧ ContinuousOn (fun z : Real × Real
    => fTime z.1 z.2) (Set.Ici (0 : Real) ×ˢ Set.univ) ∧ ContinuousOn (fun z : Real × Real =>
    fSpace z.1 z.2) (Set.Ici (0 : Real) ×ˢ Set.univ) ∧ ContinuousOn (fun z : Real × Real =>
    fSpace2 z.1 z.2) (Set.Ici (0 : Real) ×ˢ Set.univ)) (K : Real) (hK : 0 < K) (hBound : ∀ s x :
    Real, 0 ≤ s -> |f s x| ≤ K ∧ |fTime s x| ≤ K ∧ |fSpace s x| ≤ K ∧ |fSpace2 s x| ≤ K) (Xeps :
    Real -> NNReal -> Omega -> Real) (XepsLeft : Real -> NNReal -> Omega -> Real) (X2 : NNReal ->
    Omega -> Real) (hXepsInitial : ∀ epsilon omega, 0 < epsilon -> epsilon < 1 -> Xeps epsilon 0
    omega = X 0 omega) (hXepsLeft : ∀ epsilon : Real, 0 < epsilon -> epsilon < 1 -> ∀ᵐ omega :
    Omega ∂P, ∀ t : NNReal, 0 < t -> Tendsto (fun s : NNReal => Xeps epsilon s omega) (nhdsWithin
    t (Set.Iio t)) (nhds (XepsLeft epsilon t omega))) (hX2Representation : ∀ t omega, X2 t omega =
    triplet.drift * (t : Real) + ∫ z in Set.prod (Set.Icc (0 : Real) (t : Real)) {x : Real | 1 ≤
    |x|}, z.2 ∂(N.N omega)) (hXepsRepresentation : ∀ (epsilon : Real), 0 < epsilon -> epsilon < 1
    -> ∀ t omega, Xeps epsilon t omega = X2 t omega + (∫ z in Set.prod (Set.Icc (0 : Real) (t :
    Real)) {x : Real | epsilon < |x| ∧ |x| < 1}, z.2 ∂(N.N omega)) - (t : Real) * (∫ x in {x :
    Real | epsilon < |x| ∧ |x| < 1}, x ∂triplet.levyMeasure)) (Mε : Real -> NNReal -> Omega ->
    Real) (hMRepresentation : ∀ (epsilon : Real), 0 < epsilon -> epsilon < 1 -> ∀ t omega, Mε
    epsilon t omega = (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real)) {x : Real | epsilon < |x| ∧
    |x| < 1}, z.2 * fSpace z.1 (XepsLeft epsilon (Real.toNNReal z.1) omega) ∂(N.N omega)) - (∫ s
    in Set.Icc (0 : Real) (t : Real), (∫ x in {x : Real | epsilon < |x| ∧ |x| < 1}, x * fSpace s
    (XepsLeft epsilon (Real.toNNReal s) omega) ∂triplet.levyMeasure) ∂volume)), (∀ᵐ omega : Omega
    ∂P, ∀ t : NNReal, Tendsto (fun epsilon : Real => Xeps epsilon t omega) (nhdsWithin (0 : Real)
    (Set.Ioi 0)) (nhds (X t omega))) -> ∀ T : NNReal, 0 < T → ∀ δ : ℝ, 0 < δ → ∃ e0 : ℝ, 0 < e0 ∧
    e0 < 1 ∧ ∀ a b : ℝ, 0 < a → a < e0 → 0 < b → b < e0 → (∀ᵐ w ∂P, BddAbove ((fun t : NNReal =>
    |Mε a t w - Mε b t w|^2) '' Set.Iic T)) ∧ Integrable (fun w => sSup ((fun t : NNReal => |Mε a
    t w - Mε b t w|^2) '' Set.Iic T)) P ∧ (∫ w, sSup ((fun t : NNReal => |Mε a t w - Mε b t w|^2)
    '' Set.Iic T) ∂P) < δ := by
  intro Ω m P hP F X hLevy triplet hSigma hNoGaussian hTriplet hFiltration N
    Xleft hLeft hNLaw f fTime fSpace fSpace2 hTime hSpace hSpace2 hSmoothTime
    hSmoothSpace hJoint K hK hBound Xeps XepsLeft X2 hXepsInitial hXepsLeft
    hX2Representation hXepsRepresentation Mε hMRepresentation hConv
  have hm := Kyprianou.Ch04.exercise45SuppliedCutoffMartingaleV1 P F X hLevy triplet hNoGaussian hTriplet hFiltration N
    Xleft hLeft hNLaw f fTime fSpace fSpace2 hTime hSpace hSpace2 hSmoothTime
    hSmoothSpace hJoint K hK hBound Xeps XepsLeft X2 hXepsInitial hXepsLeft
    hX2Representation hXepsRepresentation Mε hMRepresentation hConv
  have hC := Kyprianou.Ch04.exercise_4_5_ii_goalV3 P F X hLevy triplet hNoGaussian hTriplet hFiltration N
    Xleft hLeft hNLaw f fTime fSpace fSpace2 hTime hSpace hSpace2 hSmoothTime
    hSmoothSpace hJoint K hK hBound Xeps XepsLeft X2 hXepsInitial hXepsLeft
    hX2Representation hXepsRepresentation
  intro T hT δ hδ
  obtain ⟨e0,he0,he01,h⟩ := (hC T hT Mε
    (fun e he he1 => ⟨hMRepresentation e he he1,(hm e he he1).1⟩)).2 δ hδ
  refine ⟨e0,he0,he01,?_⟩
  intro a b ha ha0 hb hb0
  have hMa := hm a ha (ha0.trans he01)
  have hMb := hm b hb (hb0.trans he01)
  let D := Mε a - Mε b
  have hr : ∀ᵐ w ∂P, ∀ t : NNReal, Tendsto (fun s => D s w)
      (nhdsWithin t (Ioi t)) (nhds (D t w)) := by
    filter_upwards [hMa.2.2,hMb.2.2] with w h1 h2
    exact fun t => (h1 t).sub (h2 t)
  have hL2 : Integrable (fun w => (D T w)^2) P := by
    have hA := (memLp_two_iff_integrable_sq
      ((hMa.1.stronglyAdapted T).mono (F.le T)).aestronglyMeasurable).mpr (hMa.2.1 T)
    have hB := (memLp_two_iff_integrable_sq
      ((hMb.1.stronglyAdapted T).mono (F.le T)).aestronglyMeasurable).mpr (hMb.2.1 T)
    exact (hA.sub hB).integrable_sq
  exact ⟨Kyprianou.Ch04.rightContinuousMartingaleCompactBddV1 P F D
    (hMa.1.sub hMb.1) T hT hr hL2,h a b ha ha0 hb hb0⟩
