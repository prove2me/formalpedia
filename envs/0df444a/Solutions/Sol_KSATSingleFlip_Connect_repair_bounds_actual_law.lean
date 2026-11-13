-- Prove2me | solution 1 for KSATSingleFlip.Connect.repair_bounds_actual_law
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:45:54.590331+00:00
-- url     : https://prove2.me/submissions/d9642421-a0c8-4b56-814d-2273a13a2fae
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_KSATSingleFlip_Connect_repair_bounds_fixed_start_invariance
import Theorems.Thm_KSATSingleFlip_Connect_repair_bounds_uniform_start

open scoped Classical BigOperators
open OAI.FixedClauseThreshold KSATSingleFlip.Connect

theorem solution :
    ∃ k0 : ℕ, ∀ k ≥ k0, ∃ n0 : ℕ, ∀ n ≥ n0, ∀ m : ℝ, 0 ≤ m →
      m ≤ (2 : ℝ) ^ k * n / k * loosenessLambda k →
      ∀ (z : Fin n → Bool) (t : ℕ),
        1 - Real.exp (-(rho k ^ 8) * n) ≤
          poisExp (allClauses n k) m (fun l =>
            uprob fun s : Fin t → Fin n × Bool =>
              let Φ := ofList l
              let I0 := satIdx Φ z
              let X := glauberState (subF Φ I0) z s
              RepairBounds k Φ I0 X) := by
  obtain ⟨k0, hk⟩ := repair_bounds_uniform_start
  refine ⟨k0, ?_⟩
  intro k hk0
  obtain ⟨n0, hn⟩ := hk k hk0
  refine ⟨n0, ?_⟩
  intro n hn0 m hm hupper z t
  let P : (Fin n → Bool) → ℝ := fun q => poisExp (allClauses n k) m (fun l =>
    uprob fun s : Fin t → Fin n × Bool =>
      let Φ := ofList l
      let I0 := satIdx Φ q
      let X := glauberState (subF Φ I0) q s
      RepairBounds k Φ I0 X)
  have havg : 1 - Real.exp (-(rho k ^ 8) * n) ≤ uexp P := hn n hn0 m hm hupper t
  have hconst : P = fun _ => P z := by
    funext q
    exact repair_bounds_fixed_start_invariance k m q z t
  rw [hconst] at havg
  have hcard : (Fintype.card (Fin n → Bool) : ℝ) ≠ 0 := by
    have : 0 < Fintype.card (Fin n → Bool) := Fintype.card_pos_iff.mpr ⟨fun _ => false⟩
    exact_mod_cast ne_of_gt this
  simpa [uexp, hcard, P] using havg

#print axioms solution
