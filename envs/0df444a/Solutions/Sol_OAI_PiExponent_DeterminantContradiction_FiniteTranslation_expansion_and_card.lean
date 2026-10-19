-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.expansion_and_card
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T22:21:53.954143+00:00
-- url     : https://prove2.me/submissions/a7bb616c-b405-48c3-b125-838628b2cd15

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_actualMatrix_entry_translation
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_choice_card_le_translationEnvelope
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem solution
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H)
    (selection : Row d H → Column d H) :
    (actualMinor d H selection).det = (∑ f : Family d H, term d selection f) ∧
      (Fintype.card (Family d H) : ℝ) ≤
        translationEnvelope d.m d.v0 H ^ actualRowCount d H := by
  classical
  constructor
  · let C : (r : Row d H) → Choice d H r → Row d H → ℂ :=
      fun r t c => PowerSeries.coeff (r.2.1 0 - (t.2.2 : ℕ))
        ((periodModel r.1.val ((selection c).1 0)
          (fun i => (selection c).1 i.succ)).coeff
            (InterpolationMatrix.exponentVector t.1.1))
    have hrows : actualMinor d H selection =
        (fun r => ∑ t : Choice d H r, scalar d r t • C r t) := by
      funext r c
      change actualMatrix d H r (selection c) = _
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, C] using
        (actualMatrix_entry_translation d hH r (selection c))
    calc
      (actualMinor d H selection).det =
          Matrix.det (fun r => ∑ t : Choice d H r, scalar d r t • C r t) :=
        congrArg Matrix.det hrows
      _ = ∑ f : Family d H,
          Matrix.det (fun r => scalar d r (f r) • C r (f r)) :=
        (Matrix.detRowAlternating :
          (Row d H → ℂ) [⋀^Row d H]→ₗ[ℂ] ℂ).toMultilinearMap.map_sum
            (fun r t => scalar d r t • C r t)
      _ = ∑ f : Family d H, term d selection f := by
        apply Finset.sum_congr rfl
        intro f _
        exact Matrix.det_mul_column (fun r => scalar d r (f r))
          (coefficientMatrix d selection f)
  · calc
      (Fintype.card (Family d H) : ℝ) =
          ∏ r : Row d H, (Fintype.card (Choice d H r) : ℝ) := by
        simp only [Family, Fintype.card_pi, Nat.cast_prod]
      _ ≤ ∏ _r : Row d H, translationEnvelope d.m d.v0 H :=
        Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
          (fun r _ => choice_card_le_translationEnvelope d hH r)
      _ = translationEnvelope d.m d.v0 H ^ actualRowCount d H := by
        simp only [Finset.prod_const, Finset.card_univ, actualRowCount]
