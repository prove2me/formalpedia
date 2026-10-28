-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.stepIocMul_eval_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:05:18.764635+00:00
-- url     : https://prove2.me/submissions/9f9f2044-a5e0-44eb-aa49-8184d363c58b

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoPullOut

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Modified 2026-10-12 by the KLS formalization project: ported to Lean v4.33.0 and
-- Mathlib db584cd. The changes are listed in vendor/README.md and vendor/port.patch.
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoPullOut.lean; Apache-2.0; locally patched, see formalization/vendor/port.patch; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
theorem solution {a b : ℝ} (ha : 0 < a) (hab : a < b) {V : Ω → ℝ}
    (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M) (hVm : Measurable V) (s : ℝ) (ω : Ω) :
    (LevyStochCalc.Brownian.Ito.stepIocMul Ω ha hab V hVb hVm).eval s ω = V ω * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s := by
  have hrw : (LevyStochCalc.Brownian.Ito.stepIocMul Ω ha hab V hVb hVm).eval s ω
      = ∑ i : Fin 2, if (![0, a, b] : Fin 3 → ℝ) i.castSucc < s
            ∧ s ≤ (![0, a, b] : Fin 3 → ℝ) i.succ
          then (![fun _ => (0 : ℝ), V] : Fin 2 → Ω → ℝ) i ω else 0 := rfl
  rw [hrw, Fin.sum_univ_two]
  change _ = V ω * (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s
  by_cases h : a < s ∧ s ≤ b
  · rw [Set.indicator_of_mem (Set.mem_Ioc.mpr h)]
    simp [h]
  · rw [Set.indicator_of_notMem fun hmem => h (Set.mem_Ioc.mp hmem)]
    show (if (0 : ℝ) < s ∧ s ≤ a then (0 : ℝ) else 0)
      + (if a < s ∧ s ≤ b then V ω else 0) = V ω * 0
    simp only [ite_self, zero_add]
    rw [if_neg h]
    ring
