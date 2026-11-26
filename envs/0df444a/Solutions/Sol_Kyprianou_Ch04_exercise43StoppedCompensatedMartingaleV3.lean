-- Prove2me | solution 1 for Kyprianou.Ch04.exercise43StoppedCompensatedMartingaleV3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:56:12.335325+00:00
-- url     : https://prove2.me/submissions/c48ab3c8-5cfb-4e3c-b6f7-07eb5c393108

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Theorems.Thm_Kyprianou_Ch04_exercise43GeneratorThresholdStoppingV3
import Theorems.Thm_Kyprianou_Ch04_discountedJumpKernelRegularity
import Theorems.Thm_Kyprianou_Ch04_signedCompensatedStoppedJumpTrueMartingale
import Theorems.Thm_Kyprianou_Ch04_cadlagLeftPathClockAE
import Theorems.Thm_Kyprianou_Ch04_martingaleCongrOfNullCompleteFiltration
import Theorems.Thm_Kyprianou_Ch04_clippedClockCoe
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false


open Kyprianou.Ch04

/-- Exercise 4.3(ii), with explicit regularity and finite stopped absolute mass. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (X : NNReal → Ω → ℝ) (hLevy : ProbabilityTheory.IsLevyProcess X P)
    (hAdapted : ∀ t : NNReal, Measurable[(F t)] (fun w : Ω => X t w))
    (T : ProbabilityTheory.LevyKhintchineTriple)
    [SigmaFinite T.levyMeasure]
    (hTriplet : ∀ (t : NNReal) (theta : ℝ),
      charFun (P.map (X t)) theta = Complex.exp (((t : ℝ) : Complex) *
          Kyprianou.Ch01.levyTripleExponent T theta))
    (hBV : T.gaussianVariance = 0 ∧ (∫⁻ x in Set.Ioo (-1 : ℝ) 1,
        ENNReal.ofReal |x| ∂T.levyMeasure) < ⊤)
    (hNonLattice : T.levyMeasure Set.univ < ⊤ ->
      ¬ ∃ a : ℝ, 0 < a ∧ T.levyMeasure
          {x : ℝ | ∃ k : Int, x = (k : ℝ) * a} =
        T.levyMeasure Set.univ)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (lam : ℝ) (hlambda : 0 ≤ lam)
    (hEigen : MeasureTheory.Martingale
      (fun (t : NNReal) (w : Ω) => Real.exp (-lam * (t : ℝ)) * f (X t w)) F P)
    (hIntegrable : ∀ y : ℝ,
      Integrable (fun x : ℝ => f (y + x) - f y)
        T.levyMeasure)
    (L : NNReal → Ω → ℝ) (hLeft : ∀ᵐ w : Ω ∂P, ∀ t : NNReal, 0 < t →
            Tendsto (fun s : NNReal => X s w) (nhdsWithin t (Set.Iio t)) (nhds (L t w)))
          (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0,0,0}
            P T.levyMeasure)
          (hJumpLaw : ∀ᵐ w : Ω ∂P, N.N w = pathJumpMeasure X L w)
    (hRC : F.IsRightContinuous)
    (hNull : ∀ (s : NNReal) (N A : Set Ω), MeasurableSet N → P N = 0 →
      A ⊆ N → MeasurableSet[F s] A)
    (hdom : ∀ y : ℝ, ∃ r : ℝ, 0 < r ∧ ∃ b : ℝ → ℝ,
      Integrable b T.levyMeasure ∧ ∀ z ∈ Set.Icc (y-r) (y+r),
        ∀ᵐ x ∂T.levyMeasure, ‖f (z+x)-f z‖ ≤ b x)
    (hLmeas : Measurable (fun z : ℝ × Ω => L z.1.toNNReal z.2))
    (hLadapted : ∀ t : NNReal, Measurable[F t] (L t))
    (hLpast : ∀ t : NNReal, Measurable[(F t).prod inferInstance]
      (fun z : Ω × ℝ => if z.2 ∈ Set.Icc (0 : ℝ) (t : ℝ) then L z.2.toNNReal z.1 else 0))
    (hFuture : IsFutureIndependentPoissonMeasure P T.levyMeasure F N)
    (hPast : ∀ (t : NNReal) (B : Set (ℝ × ℝ)), MeasurableSet B →
      B ⊆ Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ → Measurable[F t] (fun w => N.N w B))
    (hLocal : ∀ (t : NNReal) (j : ℕ) (w : Ω),
      N.N w (Set.Icc (0 : ℝ) (t : ℝ) ×ˢ spanningSets T.levyMeasure j) ≠ ⊤)
    (hFin : ∀ (n : ℕ) (t : NNReal),
      let tau : Ω → WithTop NNReal := fun w => sInf {v : WithTop NNReal |
        ∃ u : NNReal, v = ↑u ∧ (n : ℝ) < |∫ x, (f (X u w+x)-f (X u w)) ∂T.levyMeasure|}
      (∫⁻ w, ∫⁻ s in Set.Icc (0 : ℝ) (t : ℝ), ∫⁻ x,
        ENNReal.ofReal |if (s.toNNReal : WithTop NNReal) ≤ tau w then
          Real.exp (-lam*s)*(f (L s.toNNReal w+x)-f (L s.toNNReal w))
          else 0| ∂T.levyMeasure ∂volume ∂P) < ⊤) :
    let M : NNReal → Ω → ℝ := fun t w => (∫ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ,
        Real.exp (-lam * z.1) * (f (L z.1.toNNReal w + z.2) - f (L z.1.toNNReal w)) ∂(N.N w)) -
      (∫ s in Set.Icc (0 : ℝ) (t : ℝ), Real.exp (-lam * s) *
        (∫ x, (f (X s.toNNReal w + x) - f (X s.toNNReal w)) ∂T.levyMeasure) ∂volume)
    ∃ stop : ℕ → Ω → NNReal → NNReal,
      (∀ (n : ℕ) w t, let tau : WithTop NNReal := sInf {v : WithTop NNReal |
        ∃ s : NNReal, v = ↑s ∧ (n : ℝ) < |∫ x, (f (X s w+x)-f (X s w)) ∂T.levyMeasure|}
        (stop n w t : WithTop NNReal) = min (t : WithTop NNReal) tau) ∧
      ∀ n, Martingale (fun t w => M (stop n w t) w) F P := by
  let tau : ℕ → Ω → WithTop NNReal := fun n w => sInf {v : WithTop NNReal |
    ∃ u : NNReal, v = ↑u ∧ (n : ℝ) < |∫ x, (f (X u w+x)-f (X u w)) ∂T.levyMeasure|}
  let c := fun n w (t : NNReal) => (min (tau n w) (t : WithTop NNReal)).untopD t
  let k := fun s x w => Real.exp (-lam*s)*(f (L s.toNNReal w+x)-f (L s.toNNReal w))
  refine ⟨c,?_,?_⟩
  · intro n w t
    exact (clippedClockCoe (tau n w) t).trans (min_comm _ _)
  · intro n
    have htau : IsStoppingTime F (tau n) :=
      exercise43GeneratorThresholdStoppingV3 P F X hLevy hAdapted T hTriplet hBV
        hNonLattice f hf lam hlambda hEigen hIntegrable hRC hNull hdom n
    obtain ⟨hm,ha,hc,hkp⟩ := discountedJumpKernelRegularity P F X L f hf.continuous
      lam hLmeas hLadapted hLpast hLeft
    have hM := signedCompensatedStoppedJumpTrueMartingale P T.levyMeasure F N hFuture
      (tau n) htau k hm ha hc hPast hLocal hkp (hFin n)
    apply martingaleCongrOfNullCompleteFiltration P F hNull _ _ hM
    intro t
    filter_upwards [hLevy.cadlag_ae,hLeft] with w hw hr
    have hpath := cadlagLeftPathClockAE (fun u => X u w) (fun u => L u w)
      (fun u => (hw u).1) hr
    have hpath' := ae_restrict_of_ae_restrict_of_subset
      (show Set.Icc (0 : ℝ) (c n w t : ℝ) ⊆ Set.Ici (0 : ℝ) from fun _ hs => hs.1) hpath
    dsimp only [c] at hpath'
    dsimp only [k]
    congr 1
    apply integral_congr_ae
    filter_upwards [hpath'] with s hs
    rw [← integral_const_mul,hs]
