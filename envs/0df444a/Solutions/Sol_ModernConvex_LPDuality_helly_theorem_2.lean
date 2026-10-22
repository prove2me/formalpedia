-- Prove2me | solution 2 for ModernConvex.LPDuality.helly_theorem
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:27:10.884179+00:00
-- url     : https://prove2.me/submissions/11a80717-139c-4e8a-abf6-d14fc674be6b

import Mathlib
set_option autoImplicit false

theorem solution {n M : ℕ} (A : Fin M → Set (Fin n → ℝ)) (hconv : ∀ i, Convex ℝ (A i))
    (hinter : ∀ S : Finset (Fin M), S.card ≤ n + 1 → (⋂ i ∈ S, A i).Nonempty) :
    (⋂ i, A i).Nonempty := by
  have h := Convex.helly_theorem' (𝕜 := ℝ) (F := A) (s := Finset.univ) (fun i _ => hconv i)
    (fun I _ hI => by simpa using hinter I (by simpa using hI))
  simpa using h
