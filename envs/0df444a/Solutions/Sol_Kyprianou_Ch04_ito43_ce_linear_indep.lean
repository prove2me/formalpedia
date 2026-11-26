-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_ce_linear_indep
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:17:50.824463+00:00
-- url     : https://prove2.me/submissions/2b2cee76-cb67-406c-805f-d7200abc7895

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch04_ito43_ce_binary_events_factor
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Deterministic drift increments form independent families. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] :
    HasIndependentIncrements (fun (t : NNReal) (_ : Ω) => (t : ℝ)) P := by
  classical
  let X : NNReal → Ω → ℝ := fun t _ => (t : ℝ)
  change HasIndependentIncrements X P
  intro n u hu
  rw [iIndepFun_iff]
  intro S A hA
  have hs (k : Fin n) (hk : k ∈ S) : A k = ∅ ∨ A k = univ := by
    apply MeasurableSpace.measurableSet_bot_iff.mp
    have H := hA k hk
    change MeasurableSet[MeasurableSpace.comap
      (fun _ : Ω => (u k.succ : ℝ) - (u k.castSucc : ℝ)) inferInstance] (A k) at H
    rw [show MeasurableSpace.comap (fun _ : Ω => (u k.succ : ℝ) - (u k.castSucc : ℝ))
      (inferInstance : MeasurableSpace ℝ) = ⊥ from MeasurableSpace.comap_const _] at H
    exact H
  exact Kyprianou.Ch04.ito43_ce_binary_events_factor P S A hs
