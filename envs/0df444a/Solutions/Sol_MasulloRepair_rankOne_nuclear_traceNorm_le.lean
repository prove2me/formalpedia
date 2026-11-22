-- Prove2me | solution 1 for MasulloRepair.rankOne_nuclear_traceNorm_le
-- status  : ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-21T20:30:22.174926+00:00
-- url     : https://prove2.me/submissions/88e5f274-f085-4cbe-a293-055836ce45c2

import Theorems.Thm_MasulloGRH_traceNorm_le_nuclear_series

open MasulloGRH
open InnerProductSpace

set_option maxHeartbeats 800000

theorem solution {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (x y : H) :
    MasulloGRH.IsNuclearOperator (InnerProductSpace.rankOne ℂ x y) ∧
      MasulloGRH.traceNorm (InnerProductSpace.rankOne ℂ x y) ≤ ‖x‖ * ‖y‖ := by
  let xs : ℕ → H := fun n => if n = 0 then y else 0
  let ys : ℕ → H := fun n => if n = 0 then x else 0
  have heq : (fun n => ‖xs n‖ * ‖ys n‖) =
      (fun n => if n = 0 then ‖y‖ * ‖x‖ else 0) := by
    funext n
    by_cases hn : n = 0 <;> simp [xs, ys, hn]
  have hs : Summable (fun n => ‖xs n‖ * ‖ys n‖) := by
    rw [heq]
    exact (hasSum_ite_eq 0 (‖y‖ * ‖x‖)).summable
  have hxy : ∀ u : H, HasSum (fun n => inner ℂ (xs n) u • ys n)
      ((rankOne ℂ x y) u) := by
    intro u
    have h := hasSum_ite_eq 0 (inner ℂ y u • x)
    convert h using 1
    · funext n
      by_cases hn : n = 0 <;> simp [xs, ys, hn]
    · simp [rankOne_apply]
  refine ⟨⟨xs, ys, hs, hxy⟩, ?_⟩
  have hbound := MasulloGRH.traceNorm_le_nuclear_series (rankOne ℂ x y) xs ys hs hxy
  calc
    traceNorm (rankOne ℂ x y) ≤ ∑' m, ‖xs m‖ * ‖ys m‖ := hbound
    _ = ‖y‖ * ‖x‖ := by rw [heq, tsum_ite_eq]
    _ = ‖x‖ * ‖y‖ := by ac_rfl
