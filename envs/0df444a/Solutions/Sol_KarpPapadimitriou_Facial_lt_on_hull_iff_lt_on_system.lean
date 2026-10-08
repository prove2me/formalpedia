-- Prove2me | solution 1 for KarpPapadimitriou.Facial.lt_on_hull_iff_lt_on_system
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T04:17:27.635922+00:00
-- url     : https://prove2.me/submissions/77ae0bf6-6e05-40fa-892d-9f002ddf149a

import Mathlib
import Definitions.Def_KarpPapadimitriou_Facial_FacialDescription

open KarpPapadimitriou.Facial

theorem solution (C : COP) (F : Triples C) (hF : IsFacialDescription C F)
    (z : List Bool) (hz : z ∈ C.L) (c : Fin (C.n z) → ℤ) (k : ℤ) :
    (∀ x ∈ hull C z, (fun j => (c j : ℚ)) ⬝ᵥ x < (k : ℚ)) ↔
      ∀ x : Fin (C.n z) → ℚ,
        (∀ (f : Fin (C.n z) → ℤ) (g : ℤ),
            (⟨z, (f, g)⟩ : Σ z : List Bool, (Fin (C.n z) → ℤ) × ℤ) ∈ F →
              (fun j => (f j : ℚ)) ⬝ᵥ x ≤ (g : ℚ)) →
          (fun j => (c j : ℚ)) ⬝ᵥ x < (k : ℚ) := by
  constructor
  · intro h x hx
    exact h x ((hF.2 z hz x).mpr hx)
  · intro h x hx
    exact h x ((hF.2 z hz x).mp hx)

#print axioms solution

