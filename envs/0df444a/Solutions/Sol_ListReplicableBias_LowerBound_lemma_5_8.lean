-- Prove2me | solution 1 for ListReplicableBias.LowerBound.lemma_5_8
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T21:54:24.33087+00:00
-- url     : https://prove2.me/submissions/9be3400f-b90f-4977-a29d-64f37ceb93d2

import Mathlib
import Definitions.Def_ListReplicableBias_LowerBound_ListReplicability

noncomputable section

open MeasureTheory
open scoped ENNReal
namespace ListReplicableBias.LowerBound

/-- Lemma 5.8, PDF p. 6, for every member of every accurate list. -/
theorem _root_.solution {d : ℕ} (ε : ℝ) (hε : 0 < ε)
    (p q : Fin d → ℝ) (hp : p ∈ cube d 0 1) (hq : q ∈ cube d 0 1)
    (Lp Lq : Finset (Fin d → ℝ))
    (hLp : ∀ y ∈ Lp, ‖y - p‖ ≤ ε) (hLq : ∀ y ∈ Lq, ‖y - q‖ ≤ ε)
    (y : Fin d → ℝ) (hy : y ∈ Lp) (hpq : 2 * ε < ‖p - q‖) :
    y ∉ Lq := by
  intro hq'
  have h1 := hLp y hy
  have h2 := hLq y hq'
  have : ‖p - q‖ ≤ ‖y - p‖ + ‖y - q‖ := by
    rw [norm_sub_rev y p]
    exact norm_sub_le_norm_sub_add_norm_sub p y q
  linarith


end ListReplicableBias.LowerBound

