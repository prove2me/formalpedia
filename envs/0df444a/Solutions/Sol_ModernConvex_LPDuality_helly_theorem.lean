-- Prove2me | solution 1 for ModernConvex.LPDuality.helly_theorem
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T11:57:43.75599+00:00
-- url     : https://prove2.me/submissions/b7bd49b4-be1d-4b22-aaf1-89d6e35618e9

import Mathlib

theorem solution {n M : ℕ} (A : Fin M → Set (Fin n → ℝ)) (hconv : ∀ i, Convex ℝ (A i))
    (hinter : ∀ S : Finset (Fin M), S.card ≤ n + 1 → (⋂ i ∈ S, A i).Nonempty) :
    (⋂ i, A i).Nonempty := by
  have h := Convex.helly_theorem' (𝕜 := ℝ) (F := A) (s := Finset.univ) (fun i _ => hconv i)
    (fun I _ hI => hinter I (by simpa using hI))
  simpa using h
