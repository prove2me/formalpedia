-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45FixedCutoffGridPathwiseV5
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T19:59:25.858641+00:00
-- url     : https://prove2.me/submissions/75685b39-69b1-4f62-82eb-7b85bf482e25

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_actualRetainedFiniteAtomsAEV1
import Theorems.Thm_Kyprianou_Ch04_physicalCommonRetainedAtomAffinePathsV1
import Theorems.Thm_Kyprianou_Ch04_exercise45RetainedWeightedLedgerV5
import Theorems.Thm_Kyprianou_Ch04_continuousWeightOnLeftLimitPathV1
import Theorems.Thm_Kyprianou_Ch04_exercise45StoppedAffineUniformV4
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson Kyprianou.Ch04
open scoped NNReal ENNReal Classical
set_option autoImplicit false

/-- Apply the stopped finite affine grid limit to the actual retained atoms. -/
theorem solution :
  ∀ {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P] (F : Filtration NNReal
    (inferInstance : MeasurableSpace Omega)) (X : NNReal -> Omega -> Real) (hLevy :
    ProbabilityTheory.IsLevyProcess X P) (triplet : ProbabilityTheory.LevyKhintchineTriple) [SigmaFinite
    triplet.levyMeasure] (hNoGaussian : triplet.gaussianVariance = 0) (hTriplet : ∀ (t : NNReal) (xi : Real),
    charFun (P.map (X t)) xi = Complex.exp (((t : Real) : Complex) * Kyprianou.Ch01.levyTripleExponent triplet
    xi)) (hFiltration : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F) (N : PoissonRandomMeasure.{0,0,0} P
    triplet.levyMeasure) (Xleft : NNReal -> Omega -> Real) (hLeft : ∀ᵐ omega : Omega ∂P, ∀ t : NNReal, 0 < t
    -> Tendsto (fun s : NNReal => X s omega) (nhdsWithin t (Iio t)) (nhds (Xleft t omega))) (hNLaw : ∀ᵐ
    omega : Omega ∂P, N.N omega = Kyprianou.Ch04.pathJumpMeasure X Xleft omega) (f fTime fSpace fSpace2 : Real
    -> Real -> Real) (hTime : ∀ s x : Real, fTime s x = deriv (fun u : Real => f u x) s) (hSpace : ∀ s x :
    Real, fSpace s x = deriv (fun u : Real => f s u) x) (hSpace2 : ∀ s x : Real, fSpace2 s x = deriv (fun u :
    Real => fSpace s u) x) (hSmoothTime : ∀ x : Real, ContDiff Real 1 (fun s => f s x)) (hSmoothSpace : ∀ s :
    Real, ContDiff Real 2 (fun x => f s x)) (hJoint : ContinuousOn (fun z : Real × Real => f z.1 z.2) (Ici
    (0 : Real) ×ˢ univ) ∧ ContinuousOn (fun z : Real × Real => fTime z.1 z.2) (Ici (0 : Real) ×ˢ
    univ) ∧ ContinuousOn (fun z : Real × Real => fSpace z.1 z.2) (Ici (0 : Real) ×ˢ univ) ∧
    ContinuousOn (fun z : Real × Real => fSpace2 z.1 z.2) (Ici (0 : Real) ×ˢ univ)) (K : Real) (hK : 0
    < K) (hBound : ∀ s x : Real, 0 ≤ s -> |f s x| ≤ K ∧ |fTime s x| ≤ K ∧ |fSpace s x| ≤ K ∧ |fSpace2 s x| ≤
    K) (Xeps : Real -> NNReal -> Omega -> Real) (XepsLeft : Real -> NNReal -> Omega -> Real) (X2 : NNReal ->
    Omega -> Real) (hXepsInitial : ∀ epsilon omega, 0 < epsilon -> epsilon < 1 -> Xeps epsilon 0 omega = X 0
    omega) (hXepsLeft : ∀ epsilon : Real, 0 < epsilon -> epsilon < 1 -> ∀ᵐ omega : Omega ∂P, ∀ t : NNReal, 0 <
    t -> Tendsto (fun s : NNReal => Xeps epsilon s omega) (nhdsWithin t (Iio t)) (nhds (XepsLeft epsilon t
    omega))) (hX2Representation : ∀ t omega, X2 t omega = triplet.drift * (t : Real) + ∫ z in Set.prod
    (Icc (0 : Real) (t : Real)) {x : Real | 1 ≤ |x|}, z.2 ∂(N.N omega)) (hXepsRepresentation : ∀ (epsilon
    : Real), 0 < epsilon -> epsilon < 1 -> ∀ t omega, Xeps epsilon t omega = X2 t omega + (∫ z in Set.prod
    (Icc (0 : Real) (t : Real)) {x : Real | epsilon < |x| ∧ |x| < 1}, z.2 ∂(N.N omega)) - (t : Real) * (∫
    x in {x : Real | epsilon < |x| ∧ |x| < 1}, x ∂triplet.levyMeasure)) (Mε : Real -> NNReal -> Omega -> Real)
    (hMRepresentation : ∀ (epsilon : Real), 0 < epsilon -> epsilon < 1 -> ∀ t omega, Mε epsilon t omega = (∫ z
    in Set.prod (Icc (0 : Real) (t : Real)) {x : Real | epsilon < |x| ∧ |x| < 1}, z.2 * fSpace z.1
    (XepsLeft epsilon (Real.toNNReal z.1) omega) ∂(N.N omega)) - (∫ s in Icc (0 : Real) (t : Real), (∫ x
    in {x : Real | epsilon < |x| ∧ |x| < 1}, x * fSpace s (XepsLeft epsilon (Real.toNNReal s) omega)
    ∂triplet.levyMeasure) ∂volume)), (∀ᵐ omega : Omega ∂P, ∀ t : NNReal, Tendsto (fun epsilon : Real => Xeps
    epsilon t omega) (nhdsWithin (0 : Real) (Ioi 0)) (nhds (X t omega))) ->
      ∀ (M : NNReal → Omega → Real) (e : ℕ → ℝ), (∀ n, 0 < e n ∧ e n < 1) → Tendsto e atTop (nhds 0) →
        StronglyAdapted F M → (∀ t : NNReal, Integrable (fun w => (M t w)^2) P) → (∀ᵐ w ∂P, ∀ T : NNReal, ∀ δ
        : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ t : NNReal, t ≤ T → |Xeps (e n) t w - X t w| < δ ∧ |Mε (e n) t w -
        M t w| < δ) →
          ∀ T : NNReal,
          let G : (NNReal → Omega → ℝ) → (NNReal → Omega → ℝ) → ℕ → NNReal → Omega → ℝ := fun Y H n t w => ∑ k
            ∈ Finset.range n, H (T * (k : NNReal) / (n : NNReal)) w * (Y (min t (T * ((k+1 : ℕ) : NNReal) / (n
            : NNReal))) w - Y (min t (T * (k : NNReal) / (n : NNReal))) w)
          let Hc : ℕ → NNReal → Omega → ℝ := fun m s w => fSpace (s : ℝ) (XepsLeft (e m) s w)
          let J : ℕ → NNReal → Omega → ℝ := fun m t w => triplet.drift * (∫ s in Icc (0 : ℝ) (t : ℝ), Hc m
            s.toNNReal w) + (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}, z.2 * Hc m z.1.toNNReal w
            ∂(N.N w)) + Mε (e m) t w
          (∀ (m : ℕ), ∀ᵐ w ∂P, ∀ (δ : ℝ), 0 < δ → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ t ≤ T, |G (Xeps (e m)) (Hc m) n t w -
            J m t w| < δ) := by
  intro Ω m P hP F X hLevy triplet hSigma hNoGaussian hTriplet hFiltration N
    Xleft hLeft hNLaw f fTime fSpace fSpace2 hTime hSpace hSpace2 hSmoothTime
    hSmoothSpace hJoint K hK hBound Xeps XepsLeft X2 hXepsInitial hXepsLeft
    hX2Representation hXepsRepresentation Mε hMRepresentation hConv
  dsimp only
  intro M e he he0 hAdapt hSq hU T k
  let ε := e k
  have he' : 0 < ε := (he k).1; have he1 : ε < 1 := (he k).2
  have hAtoms := actualRetainedFiniteAtomsAEV1 P triplet.levyMeasure
    triplet.levyMeasure_isLevyMeasure N X Xleft hLevy hLeft hNLaw ε he'
  filter_upwards [hAtoms, hXepsLeft ε he' he1] with w hA hEL
  obtain ⟨S,hs,hR⟩ := hA T
  let j := fun r : NNReal => X r w - Xleft r w
  let H := fun r : NNReal => fSpace (r : ℝ) (XepsLeft ε r w)
  let c := ∫ x in {x : ℝ | ε < |x| ∧ |x| < 1}, x ∂triplet.levyMeasure
  have hy (u : NNReal) (hu : u ≤ T) : Xeps ε u w =
      (triplet.drift-c) * (u : ℝ) + ∑ r ∈ S, if r ≤ u then j r else 0 := by
    rw [hXepsRepresentation ε he' he1 u w, hX2Representation u w]
    exact (physicalCommonRetainedAtomAffinePathsV1
      (N.N w) T ε triplet.drift c he1 S j hs hR u hu).2
  have hH := continuousWeightOnLeftLimitPathV1
    (fun u => Xeps ε u w) (fun u => XepsLeft ε u w) fSpace hEL hJoint.2.2.1
  have hgrid := exercise45StoppedAffineUniformV4 T S j H
    (fun u => Xeps ε u w) (triplet.drift-c) K
    (fun r hr => ⟨(hs r hr).1,(hs r hr).2.1⟩) hy hH
    (fun r => (hBound r (XepsLeft ε r w) r.coe_nonneg).2.2.1)
  let g := fun z : ℝ × ℝ => z.2 * fSpace z.1 (XepsLeft ε z.1.toNNReal w)
  have hJ (t : NNReal) (ht : t ≤ T) :
      triplet.drift * (∫ s in Icc (0 : ℝ) (t : ℝ), H s.toNNReal) +
        (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}, z.2 * H z.1.toNNReal ∂(N.N w)) + Mε ε t w =
      (triplet.drift-c) * (∫ s in Icc (0 : ℝ) (t : ℝ), H s.toNNReal) +
        ∑ r ∈ S, if r ≤ t then j r * H r else 0 := by
    have hh := exercise45RetainedWeightedLedgerV5 (N.N w)
      triplet.levyMeasure T ε triplet.drift he1 S j hs hR
      (fun s => fSpace s (XepsLeft ε s.toNNReal w)) t ht
    have hTimeInt : (∫ s in Icc (0 : ℝ) (t : ℝ), H s.toNNReal) =
        ∫ s in Icc (0 : ℝ) (t : ℝ), fSpace s (XepsLeft ε s.toNNReal w) := by
      apply setIntegral_congr_fun measurableSet_Icc; intro s hs'
      simp [H, Real.coe_toNNReal _ hs'.1]
    have hJumpInt : (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|},
        z.2 * H z.1.toNNReal ∂(N.N w)) = ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ
        {x : ℝ | 1 ≤ |x|}, g z ∂(N.N w) := by
      apply setIntegral_congr_fun (measurableSet_Icc.prod (measurableSet_le measurable_const measurable_id.abs))
      intro z hz; simp [g,H,Real.coe_toNNReal _ hz.1.1]
    rw [hTimeInt,hJumpInt,hMRepresentation ε he' he1 t w]
    simpa only [c,g,H,Real.toNNReal_coe] using! hh
  intro δ hδ; obtain ⟨n₀,hn₀⟩ := hgrid δ hδ
  refine ⟨n₀+1,?_⟩; intro n hn t ht
  cases n with
  | zero => omega
  | succ n =>
    have hh := hn₀ n (by omega) t ht; rw [← hJ t ht] at hh
    simpa [H,g,ε,Nat.succ_eq_add_one] using hh
