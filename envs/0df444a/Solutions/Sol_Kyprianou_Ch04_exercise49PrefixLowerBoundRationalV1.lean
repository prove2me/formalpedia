-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49PrefixLowerBoundRationalV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:55:51.962153+00:00
-- url     : https://prove2.me/submissions/8ffbfaa8-be89-4b97-8cd2-de4e523dbb83

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_openHitLtRationalWitness
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false
/-- A cadlag path lower bound on a compact prefix is equivalent to its rational samples and endpoint. -/
theorem solution
    (Y : NNReal → ℝ) (hr : ∀ t, ContinuousWithinAt Y (Ici t) t)
    (s : NNReal) (b : ℝ) :
    (∀ u : NNReal, u ≤ s → b ≤ Y u) ↔
      b ≤ Y s ∧ ∀ q : ℚ, 0 < q → (q : ℝ) < s →
        b ≤ Y (Real.toNNReal q) := by
  constructor
  · intro h
    refine ⟨h s le_rfl, ?_⟩
    intro q hq hqs
    exact h _ ((Real.toNNReal_lt_iff_lt_coe
      (show (0 : ℝ) < q by exact_mod_cast hq).le).2 hqs).le
  · rintro ⟨hs, hq⟩ u hu
    by_contra! hn
    have hus : u < s := lt_of_le_of_ne hu (fun h => (not_lt_of_ge hs) (h ▸ hn))
    have hh : sInf {v : WithTop NNReal |
        ∃ t : NNReal, v = ↑t ∧ Y t ∈ Iio b} < (s : WithTop NNReal) :=
      lt_of_le_of_lt (sInf_le ⟨u, rfl, hn⟩) (WithTop.coe_lt_coe.mpr hus)
    obtain ⟨q, hq0, hqs, hneg⟩ :=
      (Kyprianou.Ch04.openHitLtRationalWitness Y (Iio b) isOpen_Iio hr s).mp hh
    exact (not_lt_of_ge (hq q hq0 hqs)) hneg
