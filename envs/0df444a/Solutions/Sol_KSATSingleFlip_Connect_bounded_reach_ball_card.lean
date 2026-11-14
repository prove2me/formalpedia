-- Prove2me | solution 1 for KSATSingleFlip.Connect.bounded_reach_ball_card
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:27:31.462596+00:00
-- url     : https://prove2.me/submissions/e95df673-dbec-4bf5-a4fe-e0f5b4169087

import Definitions.Def_KSATSingleFlip_Connect_BoundedReach

open scoped Classical BigOperators
open KSATSingleFlip.Connect

/-- A finite branching bound gives a geometric bound on each reachability ball. -/
theorem solution {V : Type} [DecidableEq V] (neighbors : V → Finset V)
    (root : V) (d r : ℕ) (hd : ∀ u, (neighbors u).card ≤ d) :
    (boundedReachBall neighbors root r).card ≤ ∑ i ∈ Finset.range (r + 1), d^i := by
  induction r with
  | zero => simp [boundedReachBall]
  | succ r ih =>
    have hsum : (∑ i ∈ Finset.range (r + 2), d^i) =
        1 + d * ∑ i ∈ Finset.range (r + 1), d^i := by
      rw [Finset.sum_range_succ']
      simp only [pow_zero, Finset.mul_sum, pow_succ']
      omega
    rw [hsum]
    calc
      (boundedReachBall neighbors root (r+1)).card ≤
          1 + ((boundedReachBall neighbors root r).biUnion neighbors).card := by
        simpa [boundedReachBall] using Finset.card_union_le {root} ((boundedReachBall neighbors root r).biUnion neighbors)
      _ ≤ 1 + ∑ u ∈ boundedReachBall neighbors root r, (neighbors u).card :=
        Nat.add_le_add_left Finset.card_biUnion_le 1
      _ ≤ 1 + (boundedReachBall neighbors root r).card * d := by
        gcongr
        simpa [nsmul_eq_mul] using
          Finset.sum_le_card_nsmul (boundedReachBall neighbors root r) (fun u => (neighbors u).card) d
            (by intro u hu; exact hd u)
      _ ≤ 1 + d * ∑ i ∈ Finset.range (r + 1), d^i := by nlinarith


#print axioms solution
