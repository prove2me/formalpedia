-- Prove2me | solution 1 for KSATSingleFlip.Connect.good_variable_reach_card
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:37:34.412195+00:00
-- url     : https://prove2.me/submissions/6b7f6493-86d7-4baa-9e81-ff8eb8026ea0

import Definitions.Def_KSATSingleFlip_Connect_GoodReach

open scoped Classical BigOperators
namespace KSATSingleFlip.Connect

/-- A finite branching bound gives a geometric bound on each reachability ball. -/
theorem audit_reach_ball_card {V : Type} [DecidableEq V] (neighbors : V → Finset V)
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

/-- In a bipartite incidence system, each two-step variable neighborhood
has at most Dk elements, giving a geometric variable-reachability bound. -/
theorem audit_bipartite_reach_card {V C : Type} [DecidableEq V] [DecidableEq C]
    (clauses : V → Finset C) (scope : C → Finset V)
    (root : V) (D k r : ℕ)
    (hD : ∀ v, (clauses v).card ≤ D) (hk : ∀ c, (scope c).card ≤ k) :
    (boundedReachBall (fun v => (clauses v).biUnion scope) root r).card ≤
      ∑ i ∈ Finset.range (r + 1), (D*k)^i := by
  apply audit_reach_ball_card
  intro v
  calc
    ((clauses v).biUnion scope).card ≤ ∑ c ∈ clauses v, (scope c).card := Finset.card_biUnion_le
    _ ≤ (clauses v).card * k := by
      simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul (clauses v)
        (fun c => (scope c).card) k (by intro c hc; exact hk c)
    _ ≤ D * k := Nat.mul_le_mul_right k (hD v)

/-- The good two-step incidence graph has branching at most Dk. -/
theorem audit_good_variable_reach_card {n : ℕ} (Φ : GFormula (Fin n)) (D k : ℕ)
    (hwidth : ∀ c : Fin Φ.length, (vbl (Φ.get c)).card ≤ k) (u : Fin n) (r : ℕ) :
    (goodVariableReach Φ D u r).card ≤ ∑ i ∈ Finset.range (r+1), (D*k)^i := by
  apply audit_bipartite_reach_card
  · intro v
    unfold goodIncidentClauses
    by_cases h : degree Φ v ≤ D
    · simp only [h, if_true]
      convert h using 1
      unfold degree
      congr 1
      ext c
      simp [vbl]
    · simp [h]
  · exact hwidth

end KSATSingleFlip.Connect

open KSATSingleFlip.Connect
theorem solution {n : ℕ} (Φ : GFormula (Fin n)) (D k : ℕ)
    (hwidth : ∀ c : Fin Φ.length, (vbl (Φ.get c)).card ≤ k) (u : Fin n) (r : ℕ) :
    (goodVariableReach Φ D u r).card ≤ ∑ i ∈ Finset.range (r+1), (D*k)^i := by
  exact audit_good_variable_reach_card Φ D k hwidth u r

#print axioms solution
