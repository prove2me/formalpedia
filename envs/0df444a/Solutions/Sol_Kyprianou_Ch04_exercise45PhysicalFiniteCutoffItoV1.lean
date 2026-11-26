-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45PhysicalFiniteCutoffItoV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:41:50.610879+00:00
-- url     : https://prove2.me/submissions/fb50bb8c-25bb-4fbf-962c-50be2e13dbe5

import Mathlib
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Theorems.Thm_Kyprianou_Ch04_actualRetainedFiniteAtomsAEV1
import Theorems.Thm_Kyprianou_Ch04_finiteRetainedAtomPhysicalItoV1
import Theorems.Thm_Kyprianou_Ch04_physicalCommonRetainedAtomAffinePathsV1
open MeasureTheory Set Topology ProbabilityTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Apply the deterministic physical Ito identity on every finite horizon. -/
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
    Real | epsilon < |x| ∧ |x| < 1}, x ∂triplet.levyMeasure)), ∀ epsilon : Real, 0 < epsilon ->
    epsilon < 1 ->
      let M : NNReal → Omega → Real := fun t omega =>
        (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real))
        {x : Real | epsilon < |x| ∧ |x| < 1},
        z.2 * fSpace z.1 (XepsLeft epsilon (Real.toNNReal z.1) omega)
        ∂(N.N omega)) -
      (∫ s in Set.Icc (0 : Real) (t : Real),
        (∫ x in {x : Real | epsilon < |x| ∧ |x| < 1},
          x * fSpace s (XepsLeft epsilon (Real.toNNReal s) omega)
          ∂triplet.levyMeasure) ∂volume)
      let x2Integral : NNReal → Omega → Real := fun t omega =>
        triplet.drift * (∫ s in Set.Icc (0 : Real) (t : Real),
          fSpace s (XepsLeft epsilon s.toNNReal omega)) +
        ∫ z in Set.Icc (0 : Real) (t : Real) ×ˢ {x : Real | 1 ≤ |x|},
          z.2 * fSpace z.1 (XepsLeft epsilon z.1.toNNReal omega) ∂(N.N omega)
      (∀ᵐ omega : Omega ∂P, ∀ t : NNReal,
            f (t : Real) (Xeps epsilon t omega) =
              f 0 (X 0 omega) +
              (∫ s in Set.Icc (0 : Real) (t : Real),
                fTime s (Xeps epsilon (Real.toNNReal s) omega)
                ∂volume) +
              (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real))
                      {x : Real | epsilon < |x|},
                (f z.1 (XepsLeft epsilon (Real.toNNReal z.1) omega + z.2) -
                 f z.1 (XepsLeft epsilon (Real.toNNReal z.1) omega) -
                 z.2 * fSpace z.1
                   (XepsLeft epsilon (Real.toNNReal z.1) omega))
                 ∂(N.N omega)) +
              x2Integral t omega + M t omega) := by
  intro Ω m P hP F X hLevy triplet hSigma hNoGaussian hTriplet hFiltration N
    Xleft hLeft hNLaw f fTime fSpace fSpace2 hTime hSpace hSpace2 hSmoothTime
    hSmoothSpace hJoint K hK hBound Xeps XepsLeft X2 hXepsInitial hXepsLeft
    hX2Representation hXepsRepresentation e he he1
  let ν := triplet.levyMeasure
  have hAtoms := Kyprianou.Ch04.actualRetainedFiniteAtomsAEV1 P ν
    triplet.levyMeasure_isLevyMeasure N X Xleft hLevy hLeft hNLaw e he
  filter_upwards [hAtoms,hXepsLeft e he he1] with w hA hEL
  intro T
  obtain ⟨S,hs,hR⟩ := hA T
  let j := fun r : NNReal => X r w - Xleft r w
  have h := Kyprianou.Ch04.finiteRetainedAtomPhysicalItoV1 (N.N w) ν T e
    triplet.drift he1 S j hs hR (fun u => Xeps e u w) (fun u => XepsLeft e u w)
    (fun u _ => by
      rw [hXepsRepresentation e he he1 u w,hX2Representation u w]
      rfl)
    hEL f fTime fSpace
    (fun s x => hTime s x ▸ ((hSmoothTime x).differentiable (by norm_num) s).hasDerivAt)
    (fun s x => hSpace s x ▸ ((hSmoothSpace s).differentiable (by norm_num) x).hasDerivAt)
    hJoint.1 hJoint.2.1 hJoint.2.2.1
  have hX0 : X 0 w = 0 := by
    have h0 := (Kyprianou.Ch04.physicalCommonRetainedAtomAffinePathsV1 (N.N w) T e
      triplet.drift (∫ x in {x : ℝ | e < |x| ∧ |x| < 1}, x ∂ν)
      he1 S j hs hR 0 zero_le).2
    have hz : (∑ r ∈ S, if r ≤ (0 : NNReal) then j r else 0) = 0 :=
      Finset.sum_eq_zero fun r hr => if_neg (not_le.mpr (hs r hr).1)
    rw [hz,NNReal.coe_zero,mul_zero,zero_add] at h0
    rw [← hXepsInitial e w he he1,hXepsRepresentation e he he1 0 w,hX2Representation 0 w]
    simp only [NNReal.coe_zero,mul_zero,zero_add,sub_zero] at h0 ⊢
    exact h0
  rw [hX0]
  exact h
