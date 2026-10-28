-- Prove2me | solution 1 for MarkovProcess.measurable_finTail
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T00:46:09.483569+00:00
-- url     : https://prove2.me/submissions/2382b466-a95a-4b67-abda-3f21cdfdfeea

import Mathlib

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal
theorem solution {n : ℕ} :
    Measurable (Fin.tail : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) :=
  measurable_pi_lambda _ fun i => measurable_pi_apply i.succ
