-- Prove2me | solution 1 for GreenTao.varnavides_set_count
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T20:41:01.85325+00:00
-- url     : https://prove2.me/submissions/e7209df1-f7df-49ff-88ed-36fdc63eb0ca

import Theorems.Thm_GreenTao_finite_interval_szemeredi
import Theorems.Thm_GreenTao_affine_window_varnavides
import Mathlib.Tactic.Positivity

theorem solution
    (k : ℕ) (hk : 3 ≤ k) (δ : ℝ) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ B : ℕ,
      ∀ (m : ℕ+) (_ : Nat.Prime (m : ℕ)) (_ : B ≤ (m : ℕ))
        (A : Finset (ZMod (m : ℕ))),
        δ * (m : ℝ) ≤ (A.card : ℝ) →
        c ≤ GreenTao.apAvg k (fun x => if x ∈ A then 1 else 0) := by
  obtain ⟨L, hkL, hinterval⟩ :=
    GreenTao.finite_interval_szemeredi k hk (δ / 2) (by positivity)
  have hLpos : 0 < L := by omega
  refine ⟨δ / (2 * (L : ℝ) ^ 2), by positivity, L, ?_⟩
  intro m hm hLm A hA
  exact GreenTao.affine_window_varnavides k L hk hkL δ hδ hinterval m hm hLm A hA
