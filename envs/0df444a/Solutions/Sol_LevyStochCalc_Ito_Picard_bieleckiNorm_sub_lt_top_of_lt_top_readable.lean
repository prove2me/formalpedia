-- Prove2me | solution 1 for LevyStochCalc.Ito.Picard.bieleckiNorm_sub_lt_top_of_lt_top_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:22:50.868688+00:00
-- url     : https://prove2.me/submissions/13d78500-53cc-42c9-a697-aad16e898af1

import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardWindow

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardWindow.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal
universe u v
variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {n d : ℕ}
omit [MeasurableSpace E] in
/-- The Bielecki norm of a difference of two path maps of finite norm is finite. -/
theorem solution {β : ℝ} (hβ : 0 ≤ β) (T : ℝ)
    {X Y : ℝ → Ω → (Fin n → ℝ)}
    (hXm : Measurable (Function.uncurry X)) (hYm : Measurable (Function.uncurry Y))
    (hX : LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) 0 T X < ⊤) (hY : LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) 0 T Y < ⊤) :
    LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T (fun t ω i => X t ω i - Y t ω i) < ⊤ := by
  have hneg : LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) 0 T (fun t ω => -(Y t ω))
      = LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) 0 T Y := by
    unfold LevyStochCalc.Ito.Picard.bieleckiNorm
    refine iSup_congr fun t => iSup_congr fun _ => ?_
    congr 2
    exact lintegral_congr fun ω => Finset.sum_congr rfl fun i _ => by simp
  have hEq : (fun t ω i => X t ω i - Y t ω i)
      = fun t (ω : Ω) => X t ω + (fun i => -(Y t ω i)) := by
    funext t ω i
    simp [Pi.add_apply, sub_eq_add_neg]
  have hnegm : Measurable (Function.uncurry fun t (ω : Ω) => -(Y t ω)) :=
    measurable_neg.comp hYm
  have hadd := LevyStochCalc.Ito.Picard.bieleckiNorm_add_le (P := P) 0 T X (fun t ω => -(Y t ω))
    (fun t => LevyStochCalc.Ito.Picard.bieleckiNorm_inner_aemeasurable _ hXm t)
    (fun t => LevyStochCalc.Ito.Picard.bieleckiNorm_inner_aemeasurable (fun t ω => -(Y t ω)) hnegm t)
  refine lt_of_le_of_lt (LevyStochCalc.Ito.Picard.bieleckiNorm_le_bieleckiNorm_zero hβ T _) ?_
  rw [hEq]
  refine lt_of_le_of_lt hadd ?_
  rw [hneg]
  exact ENNReal.add_lt_top.mpr ⟨hX, hY⟩
