-- Prove2me | solution 1 for Kyprianou.Ch02.pointFamilyFinitePRMCoreCh02V1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T07:15:09.592174+00:00
-- url     : https://prove2.me/submissions/457f915a-5c8b-4d40-9e4a-68481084bae2

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_ProbabilityTheory_map_poissonRandomMeasure_apply

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m] [Nonempty E]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P) :
    (∀ A : Set E, MeasurableSet A →
       Measurable (fun ω => ProbabilityTheory.poissonRandomMeasure K Y ω A)) ∧
    (∀ A : Set E, MeasurableSet A → m A < ⊤ →
       P.map (fun ω => ProbabilityTheory.poissonRandomMeasure K Y ω A) =
         (ProbabilityTheory.poissonMeasure (m A).toNNReal).map
           (Nat.cast : ℕ → ENNReal)) ∧
    (∀ A : Set E, MeasurableSet A → m A < ⊤ →
       ∀ᵐ ω ∂P, ProbabilityTheory.poissonRandomMeasure K Y ω A < ⊤) := by
  constructor
  · intro A hA
    exact ProbabilityTheory.measurable_poissonRandomMeasure_apply
      hd.measurable_count hd.measurable_point hA
  constructor
  · intro A hA hfin
    exact ProbabilityTheory.map_poissonRandomMeasure_apply hd hA hfin
  · intro A hA hfin
    exact ProbabilityTheory.ae_poissonRandomMeasure_apply_lt_top hd hA hfin
