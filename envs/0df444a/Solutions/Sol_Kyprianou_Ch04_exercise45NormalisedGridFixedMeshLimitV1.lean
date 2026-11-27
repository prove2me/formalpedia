-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45NormalisedGridFixedMeshLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:30:35.20009+00:00
-- url     : https://prove2.me/submissions/180716db-e301-4b42-80e0-74be81daf152

import Theorems.Thm_Kyprianou_Ch04_boundedSecondDerivativeLipschitzV1
import Theorems.Thm_Kyprianou_Ch04_positiveLeftDifferenceBoundV1
import Theorems.Thm_Kyprianou_Ch04_clippedGridFixedMeshPerturbationV1
import Theorems.Thm_Kyprianou_Ch04_ito43_path_weight_compact_bound
import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false
theorem solution : ∀ {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure
  P] (F : Filtration NNReal (inferInstance : MeasurableSpace Omega)) (X : NNReal -> Omega -> Real)
  (hLevy : ProbabilityTheory.IsLevyProcess X P) (triplet : ProbabilityTheory.LevyKhintchineTriple)
  [SigmaFinite triplet.levyMeasure] (hNoGaussian : triplet.gaussianVariance = 0) (hTriplet : ∀ (t :
  NNReal) (xi : Real), charFun (P.map (X t)) xi = Complex.exp (((t : Real) : Complex) *
  Kyprianou.Ch01.levyTripleExponent triplet xi)) (hFiltration :
  Kyprianou.Ch03.IsCompletedNaturalFiltration P X F) (N : PoissonRandomMeasure.{0,0,0} P
  triplet.levyMeasure) (Xleft : NNReal -> Omega -> Real) (hLeft : ∀ᵐ omega : Omega ∂P, ∀ t : NNReal,
  0 < t -> Tendsto (fun s : NNReal => X s omega) (nhdsWithin t (Set.Iio t)) (nhds (Xleft t omega)))
  (hNLaw : ∀ᵐ omega : Omega ∂P, N.N omega = Kyprianou.Ch04.pathJumpMeasure X Xleft omega) (f fTime
  fSpace fSpace2 : Real -> Real -> Real) (hTime : ∀ s x : Real, fTime s x = deriv (fun u : Real => f
  u x) s) (hSpace : ∀ s x : Real, fSpace s x = deriv (fun u : Real => f s u) x) (hSpace2 : ∀ s x :
  Real, fSpace2 s x = deriv (fun u : Real => fSpace s u) x) (hSmoothTime : ∀ x : Real, ContDiff Real
  1 (fun s => f s x)) (hSmoothSpace : ∀ s : Real, ContDiff Real 2 (fun x => f s x)) (hJoint :
  ContinuousOn (fun z : Real × Real => f z.1 z.2) (Set.Ici (0 : Real) ×ˢ Set.univ) ∧ ContinuousOn
  (fun z : Real × Real => fTime z.1 z.2) (Set.Ici (0 : Real) ×ˢ Set.univ) ∧ ContinuousOn (fun z :
  Real × Real => fSpace z.1 z.2) (Set.Ici (0 : Real) ×ˢ Set.univ) ∧ ContinuousOn (fun z : Real × Real
  => fSpace2 z.1 z.2) (Set.Ici (0 : Real) ×ˢ Set.univ)) (K : Real) (hK : 0 < K) (hBound : ∀ s x :
  Real, 0 ≤ s -> |f s x| ≤ K ∧ |fTime s x| ≤ K ∧ |fSpace s x| ≤ K ∧ |fSpace2 s x| ≤ K) (Xeps : Real
  -> NNReal -> Omega -> Real) (XepsLeft : Real -> NNReal -> Omega -> Real) (X2 : NNReal -> Omega ->
  Real) (hXepsInitial : ∀ epsilon omega, 0 < epsilon -> epsilon < 1 -> Xeps epsilon 0 omega = X 0
  omega) (hXepsLeft : ∀ epsilon : Real, 0 < epsilon -> epsilon < 1 -> ∀ᵐ omega : Omega ∂P, ∀ t :
  NNReal, 0 < t -> Tendsto (fun s : NNReal => Xeps epsilon s omega) (nhdsWithin t (Set.Iio t)) (nhds
  (XepsLeft epsilon t omega))) (hX2Representation : ∀ t omega, X2 t omega = triplet.drift * (t :
  Real) + ∫ z in Set.prod (Set.Icc (0 : Real) (t : Real)) {x : Real | 1 ≤ |x|}, z.2 ∂(N.N omega))
  (hXepsRepresentation : ∀ (epsilon : Real), 0 < epsilon -> epsilon < 1 -> ∀ t omega, Xeps epsilon t
  omega = X2 t omega + (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real)) {x : Real | epsilon < |x| ∧
  |x| < 1}, z.2 ∂(N.N omega)) - (t : Real) * (∫ x in {x : Real | epsilon < |x| ∧ |x| < 1}, x
  ∂triplet.levyMeasure)) (Mε : Real -> NNReal -> Omega -> Real) (hMRepresentation : ∀ (epsilon :
  Real), 0 < epsilon -> epsilon < 1 -> ∀ t omega, Mε epsilon t omega = (∫ z in Set.prod (Set.Icc (0 :
  Real) (t : Real)) {x : Real | epsilon < |x| ∧ |x| < 1}, z.2 * fSpace z.1 (XepsLeft epsilon
  (Real.toNNReal z.1) omega) ∂(N.N omega)) - (∫ s in Set.Icc (0 : Real) (t : Real), (∫ x in {x : Real
  | epsilon < |x| ∧ |x| < 1}, x * fSpace s (XepsLeft epsilon (Real.toNNReal s) omega)
  ∂triplet.levyMeasure) ∂volume)), (∀ᵐ omega : Omega ∂P, ∀ t : NNReal, Tendsto (fun epsilon : Real =>
  Xeps epsilon t omega) (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds (X t omega))) -> ∀ (M : NNReal →
  Omega → Real) (e : ℕ → ℝ), (∀ n, 0 < e n ∧ e n < 1) → Tendsto e atTop (nhds 0) → StronglyAdapted F
  M → (∀ t : NNReal, Integrable (fun w => (M t w)^2) P) → (∀ᵐ w ∂P, ∀ T : NNReal, ∀ δ : ℝ, 0 < δ → ∃
  n₀ : ℕ, ∀ n ≥ n₀, ∀ t : NNReal, t ≤ T → |Xeps (e n) t w - X t w| < δ ∧ |Mε (e n) t w - M t w| < δ)
  → ∀ T : NNReal,
          let G := fun (Y H : NNReal → Omega → ℝ) (n : ℕ) (t : NNReal) w =>
            ∑ k ∈ Finset.range n,
              H (T * (k : NNReal) / (n : NNReal)) w *
                (Y (min t (T * ((k+1 : ℕ) : NNReal) / (n : NNReal))) w -
                 Y (min t (T * (k : NNReal) / (n : NNReal))) w)
          let H : NNReal → Omega → ℝ := fun s w => fSpace (s : ℝ) (Xleft s w)
          let Hc := fun (m : ℕ) (s : NNReal) w => fSpace (s : ℝ) (XepsLeft (e m) s w)
          let H0 : NNReal → Omega → ℝ := fun s w => if s = 0 then 0 else H s w
          let Hc0 : ℕ → NNReal → Omega → ℝ := fun m s w => if s = 0 then 0 else Hc m s w
          ∀ᵐ w ∂P, ∀ n, ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ l ≥ N,
            ∀ t ≤ T, |G (Xeps (e l)) (Hc0 l) n t w - G X H0 n t w| < δ := by
  intro Ω mΩ P hP F X hLevy triplet hSigma hNoGaussian hTriplet hFiltration N
    Xleft hLeft hNLaw f fTime fSpace fSpace2 hTime hSpace hSpace2 hSmoothTime
    hSmoothSpace hJoint K hK hBound Xeps XepsLeft X2 hXepsInitial hXepsLeft
    hX2Representation hXepsRepresentation Mε hMRepresentation hConv M e he he0 hA hSq hU T
    G H Hc H0 Hc0
  have hl : ∀ᵐ w ∂P, ∀ m, ∀ t, 0 < t →
      Tendsto (fun s => Xeps (e m) s w) (nhdsWithin t (Iio t)) (nhds (XepsLeft (e m) t w)) :=
    ae_all_iff.mpr fun m => hXepsLeft (e m) (he m).1 (he m).2
  have hLip (s : NNReal) (x y : ℝ) : |fSpace s x - fSpace s y| ≤ K * |x-y| := by
    have hf : fSpace s = deriv (f s) := funext (hSpace s)
    rw [hf]
    exact Kyprianou.Ch04.boundedSecondDerivativeLipschitzV1 (f s) K y x (hSmoothSpace s)
      (fun v => by rw [← hf,← hSpace2]; exact (hBound s v s.coe_nonneg).2.2.2)
  filter_upwards [hU,hLevy.cadlag_ae,hLeft,hl] with w hw hCad hL hl'
  obtain ⟨B,hB,hX,_⟩ := Kyprianou.Ch04.ito43_path_weight_compact_bound X Xleft w hCad hL
    (fun z => z.2) continuous_snd.continuousOn T
  intro n δ hδ
  let d := δ / (1 + (n : ℝ) * (2*K+2*B*K))
  have hd : 0 < d := div_pos hδ (by positivity)
  obtain ⟨N,hN⟩ := hw T (d/2) (by positivity)
  refine ⟨N,fun l hln t ht => ?_⟩
  let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
  have hD (s : NNReal) (hs : s ≤ T) := (hN l hln s hs).1.le
  have hW (k : ℕ) (hk : k ∈ Finset.range n) :
      |Hc0 l (u k) w-H0 (u k) w| ≤ K*(d/2) := by
    by_cases h0 : u k = 0
    · simp [Hc0,H0,h0,mul_nonneg hK.le (by positivity : 0 ≤ d/2)]
    have hu : u k ≤ T := by
      dsimp [u]
      rw [div_le_iff₀ (by exact_mod_cast (Nat.zero_lt_of_lt (Finset.mem_range.mp hk)))]
      gcongr
      exact_mod_cast (Finset.mem_range.mp hk).le
    simp only [Hc0,H0,if_neg h0,Hc,H]
    exact (hLip _ _ _).trans (mul_le_mul_of_nonneg_left
      (Kyprianou.Ch04.positiveLeftDifferenceBoundV1 _ _ _ _ T (d/2)
        (hl' l) hL hD _ hu (pos_iff_ne_zero.mpr h0)) hK.le)
  have hG := Kyprianou.Ch04.clippedGridFixedMeshPerturbationV1
    (fun s => Xeps (e l) s w) (fun s => X s w) (fun s => Hc0 l s w) (fun s => H0 s w) T u n K B (d/2) (K*(d/2)) hK.le hB (by positivity)
    (by positivity) hD hX (fun k hk => by
      by_cases h0 : u k = 0
      · simp [Hc0,h0,hK.le]
      · simpa [Hc0,Hc,h0] using (hBound (u k) (XepsLeft (e l) (u k) w)
          (u k).coe_nonneg).2.2.1) hW t ht
  have heq : (1 + (n : ℝ) * (2*K+2*B*K)) * d = δ := by
    dsimp [d]
    have hpos : 0 < 1 + (n : ℝ) * (2*K+2*B*K) := by positivity
    field_simp [ne_of_gt hpos]
  change |G (Xeps (e l)) (Hc0 l) n t w-G X H0 n t w| < δ
  exact hG.trans_lt (by nlinarith [heq,hd])
