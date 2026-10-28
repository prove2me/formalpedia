-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.stepIoc_zero_eval_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:04:50.274513+00:00
-- url     : https://prove2.me/submissions/c411005e-86e5-4d8d-a81e-fa041ef6d4b2

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
theorem solution {b : ℝ} (hb : 0 < b) (s : ℝ) (ω : Ω) :
    (LevyStochCalc.Brownian.Ito.stepIoc₀ Ω hb).eval s ω = (Set.Ioc 0 b).indicator (fun _ => (1 : ℝ)) s := by
  have hrw : (LevyStochCalc.Brownian.Ito.stepIoc₀ Ω hb).eval s ω
      = ∑ i : Fin 1, if (![0, b] : Fin 2 → ℝ) i.castSucc < s
            ∧ s ≤ (![0, b] : Fin 2 → ℝ) i.succ
          then (![fun _ => (1 : ℝ)] : Fin 1 → Ω → ℝ) i ω else 0 := rfl
  rw [hrw, Fin.sum_univ_one]
  by_cases h : (0 : ℝ) < s ∧ s ≤ b
  · rw [Set.indicator_of_mem (Set.mem_Ioc.mpr h)]
    simp [h]
  · rw [Set.indicator_of_notMem fun hm => h (Set.mem_Ioc.mp hm)]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue,
      Fin.castSucc_zero, Fin.succ_zero_eq_one]
    exact if_neg h
