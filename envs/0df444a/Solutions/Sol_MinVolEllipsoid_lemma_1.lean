-- Prove2me | solution 1 for MinVolEllipsoid.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:45:40.207589+00:00
-- url     : https://prove2.me/submissions/6f91c2e4-a341-423e-b58f-33684612f82c

import Mathlib
import Definitions.Def_MinVolEllipsoid_liftCone

open MinVolEllipsoid in
theorem solution {n : ℕ} (P : Set (Fin n → ℝ)) (hPc : IsCompact P) (hPcv : Convex ℝ P)
    (hPi : (interior P).Nonempty) (x : Fin n → ℝ) (τ : ℝ)
    (hx : (Sum.elim x (fun _ => τ) : Fin n ⊕ Unit → ℝ) ∈ liftCone P) :
    0 ≤ τ ∧ (τ = 0 → x = 0) := by
  obtain ⟨m, c, y, hc, hy, heq⟩ := hx
  have hτ : τ = ∑ s, c s := by
    have := congrFun heq (Sum.inr ())
    simpa [lift, Finset.sum_apply] using this
  refine ⟨by rw [hτ]; exact Finset.sum_nonneg (fun s _ => hc s), fun h0 => ?_⟩
  have hsum : ∑ s, c s = 0 := by rw [← hτ]; exact h0
  have hc0 : ∀ s, c s = 0 := by
    intro s
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun s _ => hc s)).mp hsum s (Finset.mem_univ _)
  funext i
  have := congrFun heq (Sum.inl i)
  simpa [lift, Finset.sum_apply, hc0] using this
