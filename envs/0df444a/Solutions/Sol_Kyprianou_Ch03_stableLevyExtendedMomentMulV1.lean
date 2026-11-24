-- Prove2me | solution 1 for Kyprianou.Ch03.stableLevyExtendedMomentMulV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T21:38:53.905613+00:00
-- url     : https://prove2.me/submissions/2e098c3c-5363-45c1-8b97-cebf6bbfce48

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Theorems.Thm_ProbabilityTheory_IsLevyProcess_indepFun_increment
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (X : ℝ≥0 → Ω → ℝ) (hX : IsLevyProcess X P) (θ : ℝ) (s u : ℝ≥0) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X (s + u) ω)) ∂P =
      (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X s ω)) ∂P) *
        ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X u ω)) ∂P := by
  let f : ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.exp (θ * z))
  have hf : Measurable f := by fun_prop
  have hind := hX.indepFun_increment (s := 0) (t := s) (u := s + u) (by positivity) le_self_add
  change IndepFun (fun ω => X s ω - X 0 ω) (fun ω => X (s + u) ω - X s ω) P at hind
  simp only [hX.start_zero, sub_zero] at hind
  have hm (t : NNReal) : AEMeasurable (X t) P := by
    have hi := (hX.stationary_increments 0 t).aemeasurable_snd
    change AEMeasurable (fun w => X t w - X 0 w) P at hi
    simpa only [hX.start_zero, sub_zero] using hi
  have hs := hm s
  have hpow (ω : Ω) :
      f (X (s + u) ω) = f (X s ω) * f (X (s + u) ω - X s ω) := by
    dsimp [f]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2 <;> ring
  have heq := ((hX.stationary_increments s u).comp hf).lintegral_eq
  change (∫⁻ ω, f (X (s + u) ω - X s ω) ∂P) = (∫⁻ ω, f (X u ω - X 0 ω) ∂P) at heq
  simp only [hX.start_zero, sub_zero] at heq
  change (∫⁻ ω, f (X (s + u) ω) ∂P) = (∫⁻ ω, f (X s ω) ∂P) * ∫⁻ ω, f (X u ω) ∂P
  simp_rw [hpow]
  rw [← heq]
  exact lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun' (hf.comp_aemeasurable hs)
    (hf.comp_aemeasurable ((hm (s + u)).sub hs)) (hind.comp hf hf)
