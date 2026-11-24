-- Prove2me | solution 1 for Kyprianou.Ch03.levy_future_path_indep_pastSigma
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T14:02:58.339258+00:00
-- url     : https://prove2.me/submissions/39dc4673-2b9c-49e1-a0a3-fe12ed844f5d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_DurrettProbability_Brownian
import Theorems.Thm_Kyprianou_Ch03_levy_shifted_process_measurable
import Theorems.Thm_Kyprianou_Ch03_levy_future_finDim_indep_pastSigma

open MeasureTheory ProbabilityTheory DurrettProbability Set
open scoped NNReal

set_option autoImplicit false

/-!
Path-level Lévy independence from `pastSigma`.

Reduction:
1. Open: shifted increments (and hence evaluations via `X 0 = 0`) are measurable.
2. Open: finite future increments are `IndepFun` of finite past evaluations on `Iic τ`.
3. Mathlib `IndepFun.process_indepFun_process` upgrades to full path `IndepFun`.
4. `comap` of the past path on `Iic τ` coincides with Durrett `pastSigma X τ`.
-/

open Kyprianou.Ch03 in
theorem solution
    {Omega : Type} [mΩ : MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (τ : NNReal) :
    Indep
      (MeasurableSpace.comap
        (fun ω (u : NNReal) => X (τ + u) ω - X τ ω)
        MeasurableSpace.pi)
      (pastSigma X τ) P := by
  set F : NNReal → Omega → ℝ := fun u ω => X (τ + u) ω - X τ ω
  have hF : ∀ u, Measurable (F u) := fun u =>
    levy_shifted_process_measurable P X hX τ u
  have hXmeas : ∀ t, Measurable (X t) := by
    intro t
    have hinc : Measurable (fun ω => X (0 + t) ω - X 0 ω) :=
      levy_shifted_process_measurable P X hX 0 t
    simpa [hX.start_zero, zero_add] using hinc
  have hXmeasIic : ∀ v : Iic τ, Measurable (fun ω => X (v : NNReal) ω) := fun v =>
    hXmeas v.1
  have hfin : ∀ (I : Finset NNReal) (J : Finset (Iic τ)),
      IndepFun
        (fun ω (u : I) => F (u : NNReal) ω)
        (fun ω (v : J) => X ((v : Iic τ) : NNReal) ω) P := by
    intro I J
    simpa [F] using levy_future_finDim_indep_pastSigma P X hX τ I J
  have hpath :
      IndepFun
        (fun ω (u : NNReal) => F u ω)
        (fun ω (v : Iic τ) => X (v : NNReal) ω) P :=
    IndepFun.process_indepFun_process hF hXmeasIic hfin
  -- Identify past comap-pi with Durrett pastSigma
  have hpast_eq :
      MeasurableSpace.comap (fun ω (v : Iic τ) => X (v : NNReal) ω) MeasurableSpace.pi =
        pastSigma X τ := by
    rw [MeasurableSpace.comap_process_pi, pastSigma]
    exact iSup_subtype'' (Iic τ) (fun s => MeasurableSpace.comap (X s) inferInstance)
  -- IndepFun ⇒ Indep of comaps; rewrite past side
  change Indep
      (MeasurableSpace.comap (fun ω u => F u ω) MeasurableSpace.pi)
      (pastSigma X τ) P
  rw [← hpast_eq]
  exact hpath
