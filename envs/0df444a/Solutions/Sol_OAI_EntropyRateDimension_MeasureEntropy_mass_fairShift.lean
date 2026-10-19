-- Prove2me | solution 1 for OAI.EntropyRateDimension.MeasureEntropy.mass_fairShift
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:21:04.274647+00:00
-- url     : https://prove2.me/submissions/12e9f761-2643-4cda-b58d-a3e8d957869a

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.MeasureEntropy
universe uι uα uβ uγ uδ
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0 < s) (u : ℝ) (j : ℤ) :
    mass (fairShift μ s) (label s u) j =
      (mass μ (label s u) j+mass μ (label s u) (j-1))/2 := by
  have hm : ∀ k : ℤ, MeasurableSet {x | label s u x = k} :=
    fun k => label_measurable s u (measurableSet_singleton k)
  unfold mass fairShift
  rw [Measure.real_def, Measure.coe_finsetSum, Finset.sum_apply, Fin.sum_univ_two]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [Measure.map_apply (by fun_prop) (hm j), Measure.map_apply (by fun_prop) (hm j)]
  have e0 : (fun x => x + (((0 : Fin 2) : ℕ) : ℝ) * s) ⁻¹' {x | label s u x = j} =
      {x | label s u x = j} := by
    ext x; simp
  have e1 : (fun x => x + (((1 : Fin 2) : ℕ) : ℝ) * s) ⁻¹' {x | label s u x = j} =
      {x | label s u x = j - 1} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq, label, Fin.val_one, Nat.cast_one, one_mul]
    rw [show (x + s) / s + u = x / s + u + 1 by field_simp; ring, Int.floor_add_one]
    omega
  simp only [Fin.val_zero, Fin.val_one] at e0 e1 ⊢
  rw [e0, e1, ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num)]
  simp only [Measure.real_def]
  ring

