-- Prove2me | solution 1 for Kyprianou.Ch04.exercise43StateExitResidualMartingales
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T11:00:36.814804+00:00
-- url     : https://prove2.me/submissions/857cd2a3-c811-4949-a9c6-c30d67792f2a

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_generatorJumpContinuityOnCompact
import Theorems.Thm_Kyprianou_Ch04_openHitStoppingTimeOfAE
import Theorems.Thm_Kyprianou_Ch04_discountedJumpKernelRegularity
import Theorems.Thm_Kyprianou_Ch04_discountedStateExitMass
import Theorems.Thm_Kyprianou_Ch04_signedCompensatedStoppedJumpTrueMartingale
import Theorems.Thm_Kyprianou_Ch04_clippedRightContinuousMartingaleComplete
import Theorems.Thm_Kyprianou_Ch04_discountedBVResidualIdentity
import Theorems.Thm_Kyprianou_Ch04_strictStoppedPrimitiveClock
import Theorems.Thm_Kyprianou_Ch04_clippedClockCoe
import Theorems.Thm_Kyprianou_Ch04_martingaleCongrOfNullCompleteFiltration
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


/-- The spatially stopped generator residual primitives are martingales. -/
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
    :
    let d := T.drift - ∫ x in Ioo (-1:ℝ) 1, x ∂T.levyMeasure
    let G := fun y : ℝ => ∫ x, (f (y+x)-f y) ∂T.levyMeasure
    let H := fun y => d*deriv f y+G y-lam*f y
    let g := fun (r : ℝ) w => Real.exp (-lam*r)*H (X r.toNNReal w)
    let tau : ℕ → Ω → WithTop NNReal := fun n w => sInf {v : WithTop NNReal |
      ∃ u : NNReal, v = ↑u ∧ (n:ℝ) < |X u w|}
    ∀ n, Martingale (fun (t : NNReal) w =>
      ∫ r in Icc (0:ℝ) (t:ℝ),
        (if (r.toNNReal : WithTop NNReal) < tau n w then g r w else 0) ∂volume) F P := by
  let G := fun y : ℝ => ∫ x, (f (y+x)-f y) ∂T.levyMeasure
  let d := T.drift - ∫ x in Ioo (-1:ℝ) 1, x ∂T.levyMeasure
  let H := fun y => d*deriv f y+G y-lam*f y
  let J := fun (t : NNReal) w => Real.exp (-lam*(t:ℝ))*f (X t w)
  let g := fun (r : ℝ) w => Real.exp (-lam*r)*H (X r.toNNReal w)
  let tau : ℕ → Ω → WithTop NNReal := fun n w => sInf {v : WithTop NNReal |
    ∃ u : NNReal, v = ↑u ∧ (n:ℝ) < |X u w|}
  let k := fun (s x : ℝ) w => Real.exp (-lam*s)*(f (L s.toNNReal w+x)-f (L s.toNNReal w))
  have hG : Continuous G := generatorJumpContinuityOnCompact T.levyMeasure f hf.continuous hdom
  have hRightJ : ∀ᵐ w ∂P, ∀ t : NNReal, ContinuousWithinAt (fun u => J u w) (Ici t) t := by
    filter_upwards [hLevy.cadlag_ae] with w hw
    intro t
    have hTime : Continuous (fun u : NNReal => Real.exp (-lam*(u:ℝ))) :=
      Real.continuous_exp.comp (continuous_const.mul NNReal.continuous_coe)
    exact hTime.continuousAt.continuousWithinAt.mul
      (hf.continuous.continuousAt.tendsto.comp (hw t).1.tendsto)
  have hStop (n : ℕ) : IsStoppingTime F (tau n) :=
    openHitStoppingTimeOfAE P F hRC hNull X hAdapted
      (hLevy.cadlag_ae.mono fun w hw t => (hw t).1)
      {y : ℝ | (n:ℝ) < |y|} (isOpen_lt continuous_const continuous_abs)
  obtain ⟨hm,ha,hc,hkp⟩ := discountedJumpKernelRegularity P F X L f hf.continuous
    lam hLmeas hLadapted hLpast hLeft
  have hCV := discountedBVResidualIdentity P X L hLevy T hTriplet hBV hLeft hXm
    f hf lam G rfl hG
  have hJ0 : Martingale (fun _ : NNReal => J 0) F P :=
    martingale_const_fun F P (hEigen.stronglyAdapted 0) (hEigen.integrable 0)
  have hM (n : ℕ) : Martingale (fun (t : NNReal) w =>
      ∫ r in Icc (0:ℝ) (t:ℝ),
        (if (r.toNNReal : WithTop NNReal) < tau n w then g r w else 0) ∂volume) F P := by
    have hComp := signedCompensatedStoppedJumpTrueMartingale P T.levyMeasure F N hFuture
      (tau n) (hStop n) k hm ha hc hPast hLocal hkp
      (discountedStateExitMass P T.levyMeasure X L f hf.continuous lam hlambda
        hIntegrable hdom hLeft n)
    have hStopped := clippedRightContinuousMartingaleComplete P F hRC hNull J hEigen
      hRightJ (tau n) (hStop n)
    apply martingaleCongrOfNullCompleteFiltration P F hNull _ _ ((hStopped.sub hJ0).sub hComp)
    intro t
    filter_upwards [hCV,hJumpLaw] with w hw hN
    let c := (min (tau n w) (t:WithTop NNReal)).untopD t
    have he := strictStoppedPrimitiveClock (fun r => g r w) (tau n w) t c
      (clippedClockCoe (tau n w) t)
    have h := hw c
    change _ = _ at h
    rw [← hN] at h
    exact h.symm.trans he.symm
  exact hM
