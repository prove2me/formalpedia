-- Prove2me | solution 1 for Kyprianou.Ch04.klsSimpleCenteredMomentV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:43:50.088698+00:00
-- url     : https://prove2.me/submissions/546e0409-a03f-4cb3-aa79-de9282162367

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Theorems.Thm_Kyprianou_Ch02_prmFiniteMarkTimeRectIntensityFiniteV1
import Theorems.Thm_Kyprianou_Ch02_prmFiniteSimpleMarkRawIntegralL2V1
import Theorems.Thm_Kyprianou_Ch02_prmSimpleMarkRawCampbellSecondMomentV1
import Theorems.Thm_Kyprianou_Ch04_klsSimpleMarkMeanV1
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Exact centred second moment of the finite signed simple-mark Poisson integral. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : PoissonRandomMeasure.{0,0,0} P ν) (B : Set ℝ)
    (hB : MeasurableSet B) (hfinite : ν B < ⊤) (g : SimpleFunc ℝ ℝ) (t : ℝ≥0) :
    let D := fun ω => (∫ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ B, g z.2 ∂(N.N ω)) -
        (t : ℝ) * ∫ x in B, g x ∂ν
    Integrable (fun ω => (D ω)^2) P ∧
      (∫ ω, (D ω)^2 ∂P) = (t : ℝ) * ∫ x in B, (g x)^2 ∂ν := by
  dsimp only
  let Y : Ω → ℝ := fun ω => ∫ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ B, g z.2 ∂(N.N ω)
  let m : ℝ := (t : ℝ) * ∫ x in B, g x ∂ν
  have hY := Kyprianou.Ch02.prmFiniteSimpleMarkRawIntegralL2V1 P ν N _
    (measurableSet_Ioc.prod hB)
    (Kyprianou.Ch02.prmFiniteMarkTimeRectIntensityFiniteV1 ν B hB hfinite 0 t) g
  change MemLp Y 2 P at hY
  have hm : (∫ ω, Y ω ∂P) = m := Kyprianou.Ch04.klsSimpleMarkMeanV1 P ν N B hB hfinite g t
  have h2 : (∫ ω, (Y ω)^2 ∂P) = (t : ℝ) * (∫ x in B, (g x)^2 ∂ν) + m^2 :=
    Kyprianou.Ch02.prmSimpleMarkRawCampbellSecondMomentV1 P ν N B hB hfinite g t
  have hD : MemLp (fun ω => Y ω - m) 2 P := hY.sub (memLp_const m)
  refine ⟨hD.integrable_sq,?_⟩
  change (∫ ω, (Y ω - m)^2 ∂P) = _
  have hi : Integrable Y P := hY.integrable (by norm_num)
  have hexp : (fun ω => (Y ω - m)^2) = fun ω => (Y ω)^2 - 2*m*Y ω + m^2 := by
    funext ω
    ring
  have hsub : Integrable (fun w => (Y w)^2 - 2*m*Y w) P :=
    hY.integrable_sq.sub (hi.const_mul (2*m))
  have hadd := integral_add hsub (integrable_const (μ := P) (m^2))
  have hsub' := integral_sub hY.integrable_sq (hi.const_mul (2*m))
  have hmul := integral_const_mul (μ := P) (2*m) Y
  rw [hexp]
  calc
    _ = (∫ w, (Y w)^2 - 2*m*Y w ∂P) + ∫ _ : Ω, m^2 ∂P := hadd
    _ = ((∫ w, (Y w)^2 ∂P) - ∫ w, 2*m*Y w ∂P) + ∫ _ : Ω, m^2 ∂P := by rw [hsub']
    _ = _ := by rw [hmul, integral_const, probReal_univ, one_smul, h2, hm]; ring
