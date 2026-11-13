-- Prove2me | solution 1 for KSATSingleFlip.Connect.lemma_7_4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T04:36:31.223194+00:00
-- url     : https://prove2.me/submissions/d4e82ce1-beee-43f5-8666-9cb1d7080cff
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_KSATSingleFlip_Connect_repair_deterministic
import Theorems.Thm_KSATSingleFlip_Connect_repair_probabilistic
open scoped Classical BigOperators
open OAI.FixedClauseThreshold KSATSingleFlip.Connect

theorem solution :
    (∀ k : ℕ, 1 ≤ k → ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (Φp : List (ProperClause n k))
      (I0 : Finset (Fin (ofList Φp).length)) (x : Fin n → Bool) (W : Finset (Fin n)),
      x ∈ sols (subF (ofList Φp) I0) →
        (∃ r i, RepairRun k (ofList Φp) I0 x (RState.init (ofList Φp) x W) r i) ∧
        (∀ (r : Option (Finset (Fin n) × (Fin n → Bool))) (i : ℕ),
          RepairRun k (ofList Φp) I0 x (RState.init (ofList Φp) x W) r i →
            (r = none ∨ ∃ U y, r = some (U, y) ∧ IsRepair (ofList Φp) x W U y) ∧
            (repairCost n Φp.length i : ℝ) ≤ C * n * (n + Φp.length)) ∧
        (∀ (s : RState (ofList Φp) x) (j : ℕ),
          RepairReach k (ofList Φp) I0 x (RState.init (ofList Φp) x W) s j →
            (repairCost n Φp.length j : ℝ) ≤ C * n * (n + Φp.length))) ∧
    (∃ k0 : ℕ, ∀ k ≥ k0, ∃ n0 : ℕ, ∀ n ≥ n0, ∀ m : ℝ, 0 ≤ m →
      m ≤ (2 : ℝ) ^ k * n / k * loosenessLambda k →
      ∀ (z : Fin n → Bool) (t D : ℕ),
        1 - Real.exp (-(rho k ^ 8) * n) ≤
          poisExp (allClauses n k) m (fun l =>
            uprob fun s : Fin t → Fin n × Bool =>
              let Φp := ofList l
              let I0 := satIdx Φp z
              let X := glauberState (subF Φp I0) z s
              Reg k D Φp → ((omittedWeak Φp I0 X).card : ℝ) ≤ rho k ^ 4 * n →
                ∀ W : Finset (Fin n), (W.card : ℝ) ≤ rho k ^ 2 * n / 2 →
                  (∃ r i, RepairRun k Φp I0 X (RState.init Φp X W) r i) ∧
                  ∀ (r : Option (Finset (Fin n) × (Fin n → Bool))) (i : ℕ),
                    RepairRun k Φp I0 X (RState.init Φp X W) r i →
                      ∃ U y, r = some (U, y) ∧ IsGoodRepair k Φp X W U y))  :=
  ⟨repair_deterministic, repair_probabilistic⟩
