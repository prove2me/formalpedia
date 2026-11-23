-- Prove2me | solution 1 for Kyprianou.Ch02.prmFiniteSimpleCharToRawKLSV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T18:43:24.404803+00:00
-- url     : https://prove2.me/submissions/e4a95a6a-6adc-46ce-8926-4bc3ca68fca3

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch02_finiteSimpleCharIntegrandDCTV1
import Theorems.Thm_Kyprianou_Ch02_realCharFunLimitOfAETendstoV1
import Theorems.Thm_Kyprianou_Ch02_prmSimpleMarkFiniteWindowIntegralAETendstoV1
import Theorems.Thm_Kyprianou_Ch02_prmFiniteSimpleMarkIntegralMeasurableKLSV1
import Theorems.Thm_Kyprianou_Ch02_prmMarkedIntegralMeasurableAmbientV1
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

/-- Transfer exact simple-mark characteristic functions to the original signed mark. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤)
    (hSimple : ∀ (f : SimpleFunc ℝ ℝ) (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (fun ω => ∫ z in
        (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), f z.2 ∂(N.N ω))) ξ =
      Complex.exp ((((t : ℝ) : ℂ)) *
        ∫ x in B,
          (Complex.exp (Complex.I * (((ξ * f x : ℝ) : ℂ))) - 1) ∂ν)) :
    ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (fun ω => ∫ z in
        (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω))) ξ =
      Complex.exp ((((t : ℝ) : ℂ)) *
        ∫ x in B,
          (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1) ∂ν) := by
  let hsm : StronglyMeasurable (fun x : ℝ => x) :=
    measurable_id.stronglyMeasurable
  let f : ℕ → SimpleFunc ℝ ℝ := fun n => hsm.approx n
  have hf : ∀ x : ℝ, Tendsto (fun n => f n x) atTop (𝓝 x) :=
    fun x => hsm.tendsto_approx x
  intro t ξ
  let R : Set (ℝ × ℝ) := Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B
  let F : ℕ → Ω → ℝ := fun n ω => ∫ z in R, f n z.2 ∂(N.N ω)
  let X : Ω → ℝ := fun ω => ∫ z in R, z.2 ∂(N.N ω)
  have hFm (n : ℕ) : Measurable (F n) :=
    Kyprianou.Ch02.prmFiniteSimpleMarkIntegralMeasurableKLSV1
      P ν N R (measurableSet_Ioc.prod hB) (f n)
  have hXm : Measurable X :=
    Kyprianou.Ch02.prmMarkedIntegralMeasurableAmbientV1
      P ν N R (measurableSet_Ioc.prod hB)
  have hFlim : ∀ᵐ ω ∂P,
      Tendsto (fun n => F n ω) atTop (𝓝 (X ω)) := by
    have h :=
      Kyprianou.Ch02.prmSimpleMarkFiniteWindowIntegralAETendstoV1
        P ν N B hB hfinite f hf 0 t
    exact h.mono fun ω hw => hw.2
  have hLeft :=
    Kyprianou.Ch02.realCharFunLimitOfAETendstoV1
      P F X hFm hXm hFlim ξ
  have hRight :=
    Kyprianou.Ch02.finiteSimpleCharIntegrandDCTV1
      ν B hB hfinite f hf ξ
  have hExp : Tendsto
      (fun n => Complex.exp ((((t : ℝ) : ℂ)) *
        ∫ x in B, (Complex.exp
          (Complex.I * (((ξ * f n x : ℝ) : ℂ))) - 1) ∂ν))
      atTop (𝓝 (Complex.exp ((((t : ℝ) : ℂ)) *
        ∫ x in B, (Complex.exp
          (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1) ∂ν))) :=
    (Complex.continuous_exp.tendsto _).comp
      (hRight.const_mul (((t : ℝ) : ℂ)))
  have heq : (fun n : ℕ => charFun (P.map (F n)) ξ) =
      (fun n => Complex.exp ((((t : ℝ) : ℂ)) *
        ∫ x in B, (Complex.exp
          (Complex.I * (((ξ * f n x : ℝ) : ℂ))) - 1) ∂ν)) := by
    funext n
    exact hSimple (f n) t ξ
  rw [heq] at hLeft
  exact tendsto_nhds_unique hLeft hExp
