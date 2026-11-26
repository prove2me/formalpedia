-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45PhysicalLargeJumpGridV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:46:41.883037+00:00
-- url     : https://prove2.me/submissions/f629d0e3-5bb2-430e-834e-c34dea27789b

import Mathlib
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Theorems.Thm_Kyprianou_Ch04_actualRetainedFiniteAtomsAEV1
import Theorems.Thm_Kyprianou_Ch04_physicalCommonRetainedAtomAffinePathsV1
import Theorems.Thm_Kyprianou_Ch04_finitePhysicalAtomsSubwindowIntegralV1
import Theorems.Thm_Kyprianou_Ch04_continuousWeightOnLeftLimitPathV1
import Theorems.Thm_Kyprianou_Ch04_finiteAffineGridIntegralLimitV1
open MeasureTheory Set Topology ProbabilityTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false

/-- Apply the uniform finite-affine grid theorem to the original large-jump path. -/
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
      let x2Integral : NNReal → Omega → Real := fun t omega =>
        triplet.drift * (∫ s in Set.Icc (0 : Real) (t : Real),
          fSpace s (XepsLeft epsilon s.toNNReal omega)) +
        ∫ z in Set.Icc (0 : Real) (t : Real) ×ˢ {x : Real | 1 ≤ |x|},
          z.2 * fSpace z.1 (XepsLeft epsilon z.1.toNNReal omega) ∂(N.N omega)
      (∀ᵐ omega : Omega ∂P, ∀ t : NNReal,
              Tendsto
                (fun n : Nat =>
                  ∑ k ∈ Finset.range n,
                    let u : NNReal := t * (k : NNReal) / (n : NNReal)
                    let v : NNReal := t * ((k + 1 : Nat) : NNReal) / (n : NNReal)
                    fSpace (u : Real) (XepsLeft epsilon u omega) *
                      (X2 v omega - X2 u omega))
                atTop (nhds (x2Integral t omega))) := by
  intro Ω m P hP F X hLevy triplet hSigma hNoGaussian hTriplet hFiltration N
    Xleft hLeft hNLaw f fTime fSpace fSpace2 hTime hSpace hSpace2 hSmoothTime
    hSmoothSpace hJoint K hK hBound Xeps XepsLeft X2 hXepsInitial hXepsLeft
    hX2Representation hXepsRepresentation e he he1
  have hAtoms := Kyprianou.Ch04.actualRetainedFiniteAtomsAEV1 P triplet.levyMeasure
    triplet.levyMeasure_isLevyMeasure N X Xleft hLevy hLeft hNLaw e he
  filter_upwards [hAtoms,hXepsLeft e he he1] with w hA hEL
  intro T
  obtain ⟨S,hs,hR⟩ := hA T
  let j := fun r : NNReal => X r w - Xleft r w
  let a := fun r => if 1 ≤ |j r| then j r else 0
  let H := fun r : NNReal => fSpace (r : ℝ) (XepsLeft e r w)
  have hy (u : NNReal) (hu : u ≤ T) : X2 u w =
      triplet.drift * (u : ℝ) + ∑ r ∈ S, if r ≤ u then a r else 0 := by
    rw [hX2Representation u w]
    exact (Kyprianou.Ch04.physicalCommonRetainedAtomAffinePathsV1 (N.N w) T e
      triplet.drift 0 he1 S j hs hR u hu).1
  have hH := Kyprianou.Ch04.continuousWeightOnLeftLimitPathV1
    (fun u => Xeps e u w) (fun u => XepsLeft e u w) fSpace hEL hJoint.2.2.1
  have h := Kyprianou.Ch04.finiteAffineGridIntegralLimitV1 T S a H (fun u => X2 u w)
    triplet.drift K (fun r hr => ⟨(hs r hr).1,(hs r hr).2.1⟩) hy hH
    (fun r => (hBound r (XepsLeft e r w) r.coe_nonneg).2.2.1)
  let D := Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | e < |x|}
  let B := Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}
  have hB : MeasurableSet B := measurableSet_Icc.prod
    (measurableSet_le measurable_const measurable_id.abs)
  have hBD : B ⊆ D := prod_mono subset_rfl (fun x hx => he1.trans_le hx)
  have hI : (∫ z in B, z.2 * fSpace z.1 (XepsLeft e z.1.toNNReal w) ∂(N.N w)) =
      ∑ r ∈ S, a r * H r := by
    rw [Kyprianou.Ch04.finitePhysicalAtomsSubwindowIntegralV1 (N.N w) D S j hR B hB hBD]
    apply Finset.sum_congr rfl
    intro r hr
    simp only [B,mem_prod,mem_Icc,mem_setOf_eq,r.coe_nonneg,true_and,
      NNReal.coe_le_coe,(hs r hr).2.1,Real.toNNReal_coe]
    by_cases h : 1 ≤ |j r| <;> simp [h,a,H]
  rw [← hI] at h
  have hTimeInt : (∫ s in Icc (0 : ℝ) (T : ℝ), H s.toNNReal) =
      ∫ s in Icc (0 : ℝ) (T : ℝ), fSpace s (XepsLeft e s.toNNReal w) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro s hs
    change fSpace (s.toNNReal : ℝ) (XepsLeft e s.toNNReal w) = _
    rw [Real.coe_toNNReal _ hs.1]
  rw [hTimeInt] at h
  exact h
