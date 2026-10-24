-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_product_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:46:28.371667+00:00
-- url     : https://prove2.me/submissions/b46e9824-39fc-4797-8d7a-688fea7b0786

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators
open MeasureTheory

theorem solution (m : Nat) (T : Real) :
    MeasureTheory.volume {p : (Fin m → Real) × Real |
      (∀ i, 0 ≤ p.1 i) ∧ 0 ≤ p.2 ∧ (∑ i, p.1 i) + p.2 < T} =
      MeasureTheory.lintegral MeasureTheory.volume (fun t : Real =>
        if 0 ≤ t ∧ t < T then
          MeasureTheory.volume {x : Fin m → Real |
            (∀ i, 0 ≤ x i) ∧ (∑ i, x i) < T - t}
        else 0) := by
  let S : Set ((Fin m → Real) × Real) := {p |
    (∀ i, 0 ≤ p.1 i) ∧ 0 ≤ p.2 ∧ (∑ i, p.1 i) + p.2 < T}
  have hS : MeasurableSet S := by
    dsimp [S]
    measurability
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm hS]
  apply lintegral_congr
  intro t
  by_cases ht : 0 ≤ t ∧ t < T
  · simp only [ht, if_pos]
    congr 1
    ext x
    simp only [S, Set.mem_preimage, Set.mem_setOf_eq, Function.comp_apply]
    constructor
    · rintro ⟨hx, ht0, hsum⟩
      exact ⟨hx, by linarith⟩
    · rintro ⟨hx, hsum⟩
      exact ⟨hx, ht.1, by linarith⟩
  · simp only [ht, if_neg]
    have hpre : (fun x => (x, t)) ⁻¹' S = ∅ := by
      ext x
      simp only [Set.mem_preimage, S, Set.mem_setOf_eq,
        Set.mem_empty_iff_false, iff_false, Function.comp_apply]
      rintro ⟨hx, ht0, hsum⟩
      apply ht
      constructor
      · exact ht0
      · have hnonneg : 0 ≤ ∑ i, x i := Finset.sum_nonneg fun i hi => hx i
        linarith
    rw [hpre]
    simp