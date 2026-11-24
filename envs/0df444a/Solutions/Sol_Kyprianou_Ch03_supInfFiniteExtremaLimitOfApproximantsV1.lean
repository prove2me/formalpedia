-- Prove2me | solution 1 for Kyprianou.Ch03.supInfFiniteExtremaLimitOfApproximantsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T11:47:44.096512+00:00
-- url     : https://prove2.me/submissions/0db7385e-8550-429b-b72f-17055f4bd58a

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LevyExtrema_SBA_runSup
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (A : Set Real) (hA : A.Nonempty) (hAb : BddAbove A) (hAl : BddBelow A)
    (B : ℕ → Set Real) (hB : ∀ n, (B n).Nonempty)
    (hsub : ∀ n, B n ⊆ A)
    (happrox : ∀ a ∈ A, ∃ u : ℕ → Real,
      (∀ n, u n ∈ B n) ∧ Tendsto u atTop (𝓝 a)) :
    Tendsto (fun n => sSup (B n)) atTop (𝓝 (sSup A)) ∧
    Tendsto (fun n => sInf (B n)) atTop (𝓝 (sInf A)) := by
  have hUp (n : ℕ) : sSup (B n) ≤ sSup A :=
    csSup_le (hB n) fun a ha => le_csSup hAb (hsub n ha)
  have hLo (n : ℕ) : sInf A ≤ sInf (B n) :=
    le_csInf (hB n) fun a ha => csInf_le hAl (hsub n ha)
  constructor
  · apply tendsto_order.2
    constructor
    · intro c hc
      have hex : ∃ a ∈ A, c < a := by
        by_contra! h
        exact (not_lt_of_ge (csSup_le hA h)) hc
      obtain ⟨a, ha, hca⟩ := hex
      obtain ⟨u, hu, hut⟩ := happrox a ha
      filter_upwards [hut.eventually (Ioi_mem_nhds hca)] with n hn
      exact lt_of_lt_of_le hn (le_csSup (hAb.mono (hsub n)) (hu n))
    · intro c hc
      exact Eventually.of_forall fun n => lt_of_le_of_lt (hUp n) hc
  · apply tendsto_order.2
    constructor
    · intro c hc
      exact Eventually.of_forall fun n => lt_of_lt_of_le hc (hLo n)
    · intro c hc
      have hex : ∃ a ∈ A, a < c := by
        by_contra! h
        exact (not_lt_of_ge (le_csInf hA h)) hc
      obtain ⟨a, ha, hac⟩ := hex
      obtain ⟨u, hu, hut⟩ := happrox a ha
      filter_upwards [hut.eventually (Iio_mem_nhds hac)] with n hn
      exact lt_of_le_of_lt (csInf_le (hAl.mono (hsub n)) (hu n)) hn
