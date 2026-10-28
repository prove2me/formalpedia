-- Prove2me | solution 1 for LevyStochCalc.Brownian.BrownianMotion.hasIndepIncrements_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:27:06.089837+00:00
-- url     : https://prove2.me/submissions/6628a33c-10c2-4d84-8271-cdd4e770addb

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_MathlibBridge
import Theorems.Thm_LevyStochCalc_Brownian_iIndep_of_indep_biSup_lt_readable

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/MathlibBridge.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
/-- A Brownian motion, read on nonnegative times, has independent increments. -/
theorem solution (W : LevyStochCalc.Brownian.BrownianMotion P) :
    HasIndepIncrements (fun t : ℝ≥0 ↦ W.W t) P := by
  intro n t ht
  refine (iIndepFun_iff_iIndep _ _ _).2 (LevyStochCalc.Brownian.iIndep_of_indep_biSup_lt_readable fun i ↦ ?_)
  have hab : ((t i.castSucc : ℝ)) ≤ (t i.succ : ℝ) :=
    NNReal.coe_le_coe.2 (ht (Fin.castSucc_le_succ i))
  have hsub : (⨆ j < i, MeasurableSpace.comap
        (fun ω ↦ W.W (t j.succ : ℝ) ω - W.W (t j.castSucc : ℝ) ω) inferInstance)
      ≤ ⨆ q ∈ Set.Iic ((t i.castSucc : ℝ)),
        MeasurableSpace.comap (W.W q) inferInstance := by
    refine iSup₂_le fun j hj ↦ ?_
    have hji : (j : ℕ) < (i : ℕ) := hj
    have hjs : ((t j.succ : ℝ)) ≤ (t i.castSucc : ℝ) := by
      refine NNReal.coe_le_coe.2 (ht ?_)
      rw [Fin.le_def]
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega
    have hjc : ((t j.castSucc : ℝ)) ≤ (t i.castSucc : ℝ) :=
      le_trans (NNReal.coe_le_coe.2 (ht (Fin.castSucc_le_succ j))) hjs
    have hmem : ∀ {r : ℝ}, r ≤ (t i.castSucc : ℝ) →
        Measurable[⨆ q ∈ Set.Iic ((t i.castSucc : ℝ)),
          MeasurableSpace.comap (W.W q) inferInstance] (W.W r) := fun {r} hr ↦
      Measurable.of_comap_le (le_iSup₂ (f := fun q (_ : q ∈ Set.Iic ((t i.castSucc : ℝ))) ↦
        MeasurableSpace.comap (W.W q) inferInstance) r hr)
    exact Measurable.comap_le ((hmem hjs).sub (hmem hjc))
  rcases eq_or_lt_of_le hab with hEq | hLt
  · have hconst : (fun ω ↦ W.W (t i.succ : ℝ) ω - W.W (t i.castSucc : ℝ) ω)
        = fun _ : Ω ↦ (0 : ℝ) := by
      funext ω; rw [hEq]; ring
    have hbot : MeasurableSpace.comap
        (fun ω ↦ W.W (t i.succ : ℝ) ω - W.W (t i.castSucc : ℝ) ω) inferInstance
        = (⊥ : MeasurableSpace Ω) := by
      rw [hconst]; exact MeasurableSpace.comap_const 0
    exact indep_of_indep_of_le_right (indep_bot_right _) (le_of_eq hbot)
  · exact indep_of_indep_of_le_left
      (W.joint_increment_independent (t i.castSucc).coe_nonneg hLt) hsub
