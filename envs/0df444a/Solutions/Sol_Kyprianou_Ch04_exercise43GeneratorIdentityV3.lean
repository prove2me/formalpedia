-- Prove2me | solution 1 for Kyprianou.Ch04.exercise43GeneratorIdentityV3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T11:03:41.631801+00:00
-- url     : https://prove2.me/submissions/cab6299c-9d50-4038-9a63-593c2f38caa4

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise43StateExitResidualMartingales
import Theorems.Thm_Kyprianou_Ch04_generatorJumpContinuityOnCompact
import Theorems.Thm_Kyprianou_Ch04_discountedStateResidualData
import Theorems.Thm_Kyprianou_Ch04_localizedResidualZeroOfPrimitive
import Theorems.Thm_Kyprianou_Ch04_continuousGeneratorZeroOfPositiveIntervals
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false


open Kyprianou.Ch04


/-- Corrected Exercise 4.3(iii): full-support generator identity. -/
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
    (hXm : ∀ᵐ w ∂P, Measurable (fun r : ℝ => X r.toNNReal w))
    (hFull : ∀ t : NNReal, 0 < t → ∀ a b : ℝ, a < b → 0 < (P.map (X t)) (Ioo a b)) :
    let d := T.drift - ∫ x in Ioo (-1:ℝ) 1, x ∂T.levyMeasure
    ∀ y : ℝ, d * deriv f y + (∫ x, (f (y+x)-f y) ∂T.levyMeasure) = lam * f y := by
  let G := fun y : ℝ => ∫ x, (f (y+x)-f y) ∂T.levyMeasure
  let d := T.drift - ∫ x in Ioo (-1:ℝ) 1, x ∂T.levyMeasure
  let H := fun y => d*deriv f y+G y-lam*f y
  let g := fun (r : ℝ) w => Real.exp (-lam*r)*H (X r.toNNReal w)
  let tau : ℕ → Ω → WithTop NNReal := fun n w => sInf {v : WithTop NNReal |
    ∃ u : NNReal, v = ↑u ∧ (n:ℝ) < |X u w|}
  have hG : Continuous G := generatorJumpContinuityOnCompact T.levyMeasure f hf.continuous hdom
  have hH : Continuous H := ((continuous_const.mul hf.continuous_deriv_one).add hG).sub
    (continuous_const.mul hf.continuous)
  have hM := exercise43StateExitResidualMartingales P F X hLevy hAdapted T hTriplet hBV
    hNonLattice f hf lam hlambda hEigen hIntegrable L hLeft N hJumpLaw hRC hNull hdom
    hLmeas hLadapted hLpast hFuture hPast hLocal hXm
  obtain ⟨C,hC,hData⟩ := discountedStateResidualData P X H hH lam hlambda hLevy.cadlag_ae hXm
  have hz := localizedResidualZeroOfPrimitive P F g tau C hC hData hM
  have hAE : ∀ᵐ w ∂P, H (X 1 w) = 0 := by
    filter_upwards [hz] with w hw
    have h := hw 1 (by norm_num)
    change Real.exp (-lam*1)*H (X (Real.toNNReal 1) w) = 0 at h
    have h1 : Real.toNNReal 1 = (1:NNReal) := by norm_num
    rw [h1] at h
    exact (mul_eq_zero.mp h).resolve_left (Real.exp_ne_zero _)
  have hMap : ∀ᵐ y ∂P.map (X 1), H y = 0 :=
    (ae_map_iff ((hAdapted 1).mono (F.le 1) le_rfl).aemeasurable
      (hH.measurable (measurableSet_singleton 0))).mpr hAE
  change ∀ y : ℝ, d*deriv f y+G y = lam*f y
  intro y
  have h := continuousGeneratorZeroOfPositiveIntervals (P.map (X 1))
    (hFull 1 (by norm_num)) H hH hMap y
  change d*deriv f y+G y-lam*f y = 0 at h
  exact sub_eq_zero.mp h
