-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49EmbeddedLevyV3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:55:34.222424+00:00
-- url     : https://prove2.me/submissions/01660687-2054-4b7f-bfec-a789e2857759

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise49EmbeddedIndependentV3
import Theorems.Thm_Kyprianou_Ch04_exercise49EmbeddedIdentDistribV3
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
open Kyprianou.Ch04
theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (j : Ω → E) (hj : MeasurableEmbedding j)
    (X : NNReal → Ω → ℝ) (Y : NNReal → E → ℝ)
    (hX : IsLevyProcess X P) (hY0 : Y 0 = fun _ => 0)
    (hAgree : ∀ t w, Y t (j w) = X t w) :
    IsLevyProcess Y (Measure.map j P) := by
  have he (s t : NNReal) : ProbabilityTheory.increment Y s t ∘ j = ProbabilityTheory.increment X s t := by
    funext w
    change Y t (j w) - Y s (j w) = X t w - X s w
    rw [hAgree,hAgree]
  refine ⟨hY0,?_,?_,?_⟩
  · intro n t ht
    apply exercise49EmbeddedIndependentV3 P j hj
    change iIndepFun (fun k : Fin n => ProbabilityTheory.increment Y (t k.castSucc) (t k.succ) ∘ j) P
    simp_rw [he]
    exact hX.indep_increments n t ht
  · intro s h
    apply exercise49EmbeddedIdentDistribV3 P j hj
    rw [he,he]
    exact hX.stationary_increments s h
  · apply hj.ae_map_iff.mpr
    filter_upwards [hX.cadlag_ae] with w hw
    simpa only [hAgree] using hw
