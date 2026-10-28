-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.stepIoc_eval_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:04:59.92086+00:00
-- url     : https://prove2.me/submissions/3763dba1-d5bd-4ea8-92f5-6c1fb03c810e

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoAlgebraAssociativity

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Modified 2026-10-12 by the KLS formalization project: ported to Lean v4.33.0 and
-- Mathlib db584cd. The changes are listed in vendor/README.md and vendor/port.patch.
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoAlgebraAssociativity.lean; Apache-2.0; locally patched, see formalization/vendor/port.patch; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
theorem solution {a b : ℝ} (ha : 0 < a) (hab : a < b) (s : ℝ) (ω : Ω) :
    (LevyStochCalc.Brownian.Ito.stepIoc Ω ha hab).eval s ω = (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s := by
  have hrw : (LevyStochCalc.Brownian.Ito.stepIoc Ω ha hab).eval s ω
      = ∑ i : Fin 2, if (![0, a, b] : Fin 3 → ℝ) i.castSucc < s
            ∧ s ≤ (![0, a, b] : Fin 3 → ℝ) i.succ
          then (![fun _ => (0 : ℝ), fun _ => (1 : ℝ)] : Fin 2 → Ω → ℝ) i ω else 0 := rfl
  rw [hrw, Fin.sum_univ_two]
  by_cases h : a < s ∧ s ≤ b
  · rw [Set.indicator_of_mem (Set.mem_Ioc.mpr h)]
    simp [h]
  · rw [Set.indicator_of_notMem fun hm => h (Set.mem_Ioc.mp hm)]
    show (if (0 : ℝ) < s ∧ s ≤ a then (0 : ℝ) else 0)
      + (if a < s ∧ s ≤ b then (1 : ℝ) else 0) = 0
    simp only [ite_self, zero_add]
    exact if_neg h
