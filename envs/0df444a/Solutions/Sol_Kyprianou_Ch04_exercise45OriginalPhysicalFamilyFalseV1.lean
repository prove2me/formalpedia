-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45OriginalPhysicalFamilyFalseV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:11:36.736118+00:00
-- url     : https://prove2.me/submissions/46ebdbcc-3874-4974-9245-1621024cd4e0

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
import Theorems.Thm_Kyprianou_Ch04_exercise45DeterministicDriftModelV1
import Theorems.Thm_Kyprianou_Ch04_exercise45BadLeftPathV1
import Theorems.Thm_Kyprianou_Ch04_exercise45ZeroTimeObstruction
import Theorems.Thm_Kyprianou_Ch04_exercise45ZeroIntensityPRM
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open Kyprianou.Ch04 Kyprianou.Ch03 Kyprianou.Ch01
open scoped NNReal ENNReal Classical
set_option autoImplicit false

/-- The old localised physical family target is false. -/
theorem solution : ¬ (∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega)) (X : NNReal -> Omega -> Real)
    (hLevy : ProbabilityTheory.IsLevyProcess X P) (triplet : ProbabilityTheory.LevyKhintchineTriple)
    [SigmaFinite triplet.levyMeasure] (hNoGaussian : triplet.gaussianVariance = 0)
    (hTriplet : ∀ (t : NNReal) (xi : Real), charFun (P.map (X t)) xi =
        Complex.exp (((t : Real) : Complex) * levyTripleExponent triplet xi))
    (hFiltration : IsCompletedNaturalFiltration P X F)
    (N : PoissonRandomMeasure.{0,0,0} P triplet.levyMeasure) (Xleft : NNReal -> Omega -> Real)
    (hLeft : ∀ᵐ omega : Omega ∂P, ∀ t : NNReal, 0 < t -> Tendsto (fun s : NNReal => X s omega)
        (nhdsWithin t (Iio t)) (nhds (Xleft t omega))) (hNLaw : ∀ᵐ omega : Omega ∂P,
      N.N omega = pathJumpMeasure X Xleft omega)
    (f fTime fSpace fSpace2 : Real -> Real -> Real) (hTime : ∀ s x : Real,
      fTime s x = deriv (fun u : Real => f u x) s) (hSpace : ∀ s x : Real,
      fSpace s x = deriv (fun u : Real => f s u) x) (hSpace2 : ∀ s x : Real,
      fSpace2 s x = deriv (fun u : Real => fSpace s u) x)
    (hSmoothTime : ∀ x : Real, ContDiff Real 1 (fun s => f s x))
    (hSmoothSpace : ∀ s : Real, ContDiff Real 2 (fun x => f s x))
    (hJoint : ContinuousOn (fun z : Real × Real => f z.1 z.2) (Ici (0 : Real) ×ˢ univ) ∧
      ContinuousOn (fun z : Real × Real => fTime z.1 z.2) (Ici (0 : Real) ×ˢ univ) ∧
      ContinuousOn (fun z : Real × Real => fSpace z.1 z.2) (Ici (0 : Real) ×ˢ univ) ∧
      ContinuousOn (fun z : Real × Real => fSpace2 z.1 z.2) (Ici (0 : Real) ×ˢ univ))
    (X2 : NNReal -> Omega -> Real) (hX2Representation : ∀ t omega, X2 t omega =
        triplet.drift * (t : Real) + ∫ z in prod (Icc (0 : Real) (t : Real))
          {x : Real | 1 ≤ |x|}, z.2 ∂(N.N omega)),
      let x2Integral : NNReal → Omega → Real := fun t omega =>
        triplet.drift * (∫ s in Icc (0 : Real) (t : Real), fSpace s (Xleft s.toNNReal omega)) +
        ∫ z in Icc (0 : Real) (t : Real) ×ˢ {x : Real | 1 ≤ |x|},
          z.2 * fSpace z.1 (Xleft z.1.toNNReal omega) ∂(N.N omega)
      ∃ (Mfamily : ℕ → NNReal → Omega → Real) (stops : Nat -> Omega -> NNReal)
          (integral : NNReal -> Omega -> Real),
          let M : NNReal → Omega → Real := fun t w =>
            if h : ∃ k : ℕ, t ≤ stops k w then Mfamily (Nat.find h) t w else 0
          (∀ᵐ w ∂P, ∀ n m : ℕ, n ≤ m → ∀ t,
            Mfamily m (min t (stops n w)) w = Mfamily n (min t (stops n w)) w) ∧
          (∀ᵐ omega : Omega ∂P, ∀ t : NNReal, integral t omega = x2Integral t omega + M t omega) ∧
          IsStochasticIntegralInProbabilityV2 P X
            (fun s omega => fSpace (s : Real) (Xleft s omega)) integral ∧ (∀ (n : Nat) (t : NNReal),
            MeasurableSet[(F t)] {omega : Omega | stops n omega ≤ t}) ∧
          (∀ᵐ omega : Omega ∂P, Monotone (fun n : Nat => stops n omega)) ∧ (∀ᵐ omega : Omega ∂P,
            Tendsto (fun n : Nat => (stops n omega : WithTop NNReal)) atTop (nhds ⊤)) ∧
          (∀ n : Nat, MeasureTheory.Martingale
            (fun t omega => Mfamily n (min t (stops n omega)) omega) F P) ∧
          (∀ᵐ omega : Omega ∂P, ∀ t : NNReal, f (t : Real) (X t omega) = f 0 (X 0 omega) +
              (∫ s in Icc (0 : Real) (t : Real), fTime s (X (Real.toNNReal s) omega) ∂volume) +
              (∫ z in prod (Icc (0 : Real) (t : Real)) univ,
                (f z.1 (Xleft (Real.toNNReal z.1) omega + z.2) -
                 f z.1 (Xleft (Real.toNNReal z.1) omega) -
                 z.2 * fSpace z.1 (Xleft (Real.toNNReal z.1) omega))
                ∂(N.N omega)) + integral t omega)) := by
  classical
  intro h
  letI m : MeasurableSpace ℕ := ⊥
  let P : Measure ℕ := Measure.dirac 0
  letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  let X : NNReal → ℕ → ℝ := fun t _ => (t : ℝ)
  let Y : NNReal → ℕ → ℝ := fun t w => if t = 0 then (w : ℝ) else (t : ℝ)
  let tr : LevyKhintchineTriple := ⟨1,0,0,by simp [IsLevyMeasure]⟩
  letI : SigmaFinite tr.levyMeasure := by dsimp [tr]; infer_instance
  let F : Filtration NNReal m := ⊥
  obtain ⟨hX,htr,hF⟩ := Kyprianou.Ch04.exercise45DeterministicDriftModelV1
  obtain ⟨N,hN⟩ := Kyprianou.Ch04.exercise45ZeroIntensityPRM P
  obtain ⟨hLeft,hPath⟩ := Kyprianou.Ch04.exercise45BadLeftPathV1 P
  have hNLaw : ∀ᵐ w ∂P, N.N w = Kyprianou.Ch04.pathJumpMeasure X Y w := by
    filter_upwards [] with w
    exact (hN w).trans (hPath w).symm
  let f : ℝ → ℝ → ℝ := fun _ x => x^2
  let ft : ℝ → ℝ → ℝ := fun _ _ => 0
  let fx : ℝ → ℝ → ℝ := fun _ x => 2*x
  let fxx : ℝ → ℝ → ℝ := fun _ _ => 2
  have hX2 (t : NNReal) (w : ℕ) : X t w =
      tr.drift * (t : ℝ) + ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}, z.2 ∂(N.N w) := by
    simp [X,tr,hN w]
  obtain ⟨Mf,stops,I,hCons,hSum,hUCP,hStop,hMono,hEx,hMart,hIto⟩ :=
    @h ℕ m P inferInstance F X hX tr inferInstance rfl htr hF N Y hLeft hNLaw
      f ft fx fxx (by intros; simp [ft,f]) (by intros; simp [fx,f,deriv_pow])
      (by intros; simp [fxx,fx,deriv_const_mul]) (by intro x; dsimp [f]; fun_prop)
      (by intro s; dsimp [f]; fun_prop)
      (by dsimp [f,ft,fx,fxx]; exact ⟨by fun_prop,by fun_prop,by fun_prop,by fun_prop⟩) X hX2
  have hI : ∀ᵐ w ∂P, ∀ t : NNReal, I t w = (t : ℝ)^2 := by
    filter_upwards [hIto] with w hw
    intro t
    simpa [f,ft,X,hN w] using (hw t).symm
  exact Kyprianou.Ch04.exercise45ZeroTimeObstruction P rfl
    (fun w : ℕ => (w : ℝ)) (fun n => ⟨n,rfl⟩) I hI hUCP
