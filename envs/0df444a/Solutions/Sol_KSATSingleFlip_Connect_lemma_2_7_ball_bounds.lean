-- Prove2me | solution 1 for KSATSingleFlip.Connect.lemma_2_7_ball_bounds
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:40:05.670209+00:00
-- url     : https://prove2.me/submissions/cb04a9d8-8141-4d77-97b4-d2d71210fd0f

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


lemma audit_adj_factor {n : ℕ} (Φ : GFormula (Fin n)) (x y : Fin n ⊕ Fin Φ.length)
    (h : (factorGraph Φ).Adj x y) :
    (∃ v c, x = Sum.inl v ∧ y = Sum.inr c ∧ v ∈ vbl (Φ.get c)) ∨
    (∃ v c, y = Sum.inl v ∧ x = Sum.inr c ∧ v ∈ vbl (Φ.get c)) := by
  simp only [factorGraph, SimpleGraph.fromRel_adj] at h
  simpa [vbl] using h.2

lemma audit_reach_prepend {V : Type} [DecidableEq V] (N : V → Finset V)
    {u b v : V} (hb : b ∈ N u) (r : ℕ) (hv : v ∈ boundedReachBall N b r) :
    v ∈ boundedReachBall N u (r+1) := by
  induction r generalizing v with
  | zero =>
    have e : v = b := by simpa [boundedReachBall] using hv
    subst v
    simp only [boundedReachBall, Finset.mem_union, Finset.mem_biUnion]
    exact Or.inr ⟨u, by simp [boundedReachBall], hb⟩
  | succ r ih =>
    simp only [boundedReachBall, Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion] at hv
    change v ∈ ({u} ∪ (boundedReachBall N u (r+1)).biUnion N)
    simp only [Finset.mem_union, Finset.mem_biUnion]
    rcases hv with rfl | ⟨z,hz,hzv⟩
    · exact Or.inr ⟨u, by simp [boundedReachBall], hb⟩
    · exact Or.inr ⟨z, ih hz, hzv⟩

lemma audit_walk_reach {n : ℕ} (Φ : GFormula (Fin n)) (D : ℕ)
    {u v : Fin n} (p : (factorGraph Φ).Walk (Sum.inl u) (Sum.inl v))
    (hgood : ∀ x : Fin n, Sum.inl x ∈ p.support → degree Φ x ≤ D) :
    v ∈ goodVariableReach Φ D u ((p.length+1)/2) := by
  induction hl : p.length using Nat.strong_induction_on generalizing u v with
  | h m ih =>
    cases p with
    | nil =>
      simp only [SimpleGraph.Walk.length_nil] at hl
      subst m
      simp [goodVariableReach, boundedReachBall]
    | @cons a b c h p =>
      have hab := audit_adj_factor Φ _ _ h
      cases b with
      | inl b => simp at hab
      | inr clause =>
        cases p with
        | @cons a b c h₂ p =>
          cases b with
          | inr b =>
            have hbad := audit_adj_factor Φ _ _ h₂
            simp at hbad
          | inl b =>
            have hu : u ∈ vbl (Φ.get clause) := by simpa using hab
            have hv : b ∈ vbl (Φ.get clause) := by
              have hh := audit_adj_factor Φ _ _ h₂
              simpa using hh
            have huD : degree Φ u ≤ D := hgood u (by simp)
            have hb : b ∈ (goodIncidentClauses Φ D u).biUnion (fun c => vbl (Φ.get c)) := by
              refine Finset.mem_biUnion.mpr ⟨clause, ?_, hv⟩
              simp only [goodIncidentClauses, huD, if_true, Finset.mem_filter, Finset.mem_univ, true_and]
              exact hu
            have hg : ∀ x : Fin n, Sum.inl x ∈ p.support → degree Φ x ≤ D := by
              intro x hx
              apply hgood x
              simp [hx]
            have hlt : p.length < m := by simp at hl; omega
            have hi := ih p.length hlt p hg rfl
            have hr := audit_reach_prepend _ hb ((p.length+1)/2) hi
            have he : (p.length+1)/2+1 = (m+1)/2 := by simp at hl; omega
            simpa [goodVariableReach, he] using hr

lemma audit_reach_mono {V : Type} [DecidableEq V] (N : V → Finset V)
    (root : V) (r : ℕ) : boundedReachBall N root r ⊆ boundedReachBall N root (r+1) := by
  induction r with
  | zero => simp [boundedReachBall]
  | succ r ih =>
    intro u hu
    simp only [boundedReachBall, Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion] at hu ⊢
    rcases hu with rfl | ⟨v, hv, huv⟩
    · exact Or.inl rfl
    · apply Or.inr
      refine ⟨v, ?_, huv⟩
      simpa only [boundedReachBall, Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion] using ih hv


lemma audit_walk_even {n : ℕ} (Φ : GFormula (Fin n)) {u v : Fin n}
    (p : (factorGraph Φ).Walk (Sum.inl u) (Sum.inl v)) : p.length % 2 = 0 := by
  induction hl : p.length using Nat.strong_induction_on generalizing u v with
  | h m ih =>
    cases p with
    | nil => simp at hl; omega
    | @cons a b c h p =>
      have hab := audit_adj_factor Φ _ _ h
      cases b with
      | inl b => simp at hab
      | inr clause =>
        cases p with
        | @cons a b c h₂ p =>
          cases b with
          | inr b =>
            have hh := audit_adj_factor Φ _ _ h₂
            simp at hh
          | inl b =>
            have hp : p.length < m := by simp at hl; omega
            have := ih p.length hp p rfl
            simp at hl
            omega

lemma audit_clause_walk_neighbor {n : ℕ} (Φ : GFormula (Fin n)) (D r : ℕ)
    {c : Fin Φ.length} {root : Fin n}
    (p : (factorGraph Φ).Walk (Sum.inr c) (Sum.inl root))
    (hgood : ∀ x : Fin n, Sum.inl x ∈ p.support → degree Φ x ≤ D)
    (hlen : p.length ≤ 2*r) :
    ∃ v ∈ goodVariableReach Φ D root (r-1), c ∈ goodIncidentClauses Φ D v := by
  cases p with
  | @cons a b e h p =>
    have ha := audit_adj_factor Φ _ _ h
    cases b with
    | inr b => simp at ha
    | inl v =>
      have hv : v ∈ vbl (Φ.get c) := by simpa using ha
      have hvgood : degree Φ v ≤ D := hgood v (by simp)
      have hg : ∀ x : Fin n, Sum.inl x ∈ p.reverse.support → degree Φ x ≤ D := by
        intro x hx
        apply hgood x
        simpa using hx
      have hr := audit_walk_reach Φ D p.reverse hg
      have heven := audit_walk_even Φ p
      have hlen' : p.length + 1 ≤ 2*r := by simpa using hlen
      have hbound : (p.reverse.length+1)/2 ≤ r-1 := by simp only [SimpleGraph.Walk.length_reverse]; omega
      have hm := (monotone_nat_of_le_succ (audit_reach_mono
        (fun v => (goodIncidentClauses Φ D v).biUnion (fun c => vbl (Φ.get c))) root)) hbound hr
      refine ⟨v, hm, ?_⟩
      simp only [goodIncidentClauses, hvgood, if_true, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hv

/-- Any variable in a locally degree-bounded metric ball is mutually
reachable through degree-truncated two-step incidences. -/
theorem audit_ball_good_reach {n : ℕ} (Φ : GFormula (Fin n)) (D r : ℕ)
    (root x : Fin n) (hdeg : ∀ v ∈ ballVars Φ root r, degree Φ v ≤ D)
    (hx : x ∈ ballVars Φ root r) :
    x ∈ goodVariableReach Φ D root r ∧ root ∈ goodVariableReach Φ D x r := by
  have hdist : withinDist Φ (Sum.inl root) (Sum.inl x) (2*r) := by simpa [ballVars] using hx
  obtain ⟨p, hp⟩ := hdist.1.exists_walk_length_eq_dist
  have plen : p.length ≤ 2*r := by simpa [hp] using hdist.2
  have hg : ∀ v : Fin n, Sum.inl v ∈ p.support → degree Φ v ≤ D := by
    intro v hv
    apply hdeg v
    change v ∈ Finset.univ.filter (fun u => withinDist Φ (Sum.inl root) (Sum.inl u) (2*r))
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change (factorGraph Φ).Reachable _ _ ∧ (factorGraph Φ).dist _ _ ≤ 2*r
    refine ⟨(p.takeUntil _ hv).reachable, ?_⟩
    exact le_trans (SimpleGraph.dist_le (p.takeUntil _ hv)) (le_trans (p.length_takeUntil_le_length hv) plen)
  have hgr : ∀ v : Fin n, Sum.inl v ∈ p.reverse.support → degree Φ v ≤ D := by
    intro v hv
    apply hg v
    simpa using hv
  have h1 := audit_walk_reach Φ D p hg
  have h2 := audit_walk_reach Φ D p.reverse hgr
  have hmono : ∀ a b : ℕ, a ≤ b → ∀ y z, y ∈ goodVariableReach Φ D z a → y ∈ goodVariableReach Φ D z b := by
    intro a b hab y z hy
    exact (monotone_nat_of_le_succ (audit_reach_mono (fun v => (goodIncidentClauses Φ D v).biUnion (fun c => vbl (Φ.get c))) z)) hab hy
  constructor
  · apply hmono _ r _ _ _ h1
    omega
  · apply hmono _ r _ _ _ h2
    simp only [SimpleGraph.Walk.length_reverse]
    omega



/-- Every clause in a degree-bounded metric ball meets a variable reached
in at most r-1 truncated two-step incidences. -/
lemma audit_ball_clause_incidence {n : ℕ} (Φ : GFormula (Fin n)) (D r : ℕ)
    (root : Fin n) (hdeg : ∀ v ∈ ballVars Φ root r, degree Φ v ≤ D) :
    ballIdx Φ root r ⊆ (goodVariableReach Φ D root (r-1)).biUnion (goodIncidentClauses Φ D) := by
  intro c hc
  have hdist : withinDist Φ (Sum.inl root) (Sum.inr c) (2*r) := by simpa [ballIdx] using hc
  obtain ⟨p, hp⟩ := hdist.1.exists_walk_length_eq_dist
  have plen : p.length ≤ 2*r := by simpa [hp] using hdist.2
  have hg : ∀ v : Fin n, Sum.inl v ∈ p.reverse.support → degree Φ v ≤ D := by
    intro v hv
    have hv' : Sum.inl v ∈ p.support := by simpa using hv
    apply hdeg v
    change v ∈ Finset.univ.filter (fun u => withinDist Φ (Sum.inl root) (Sum.inl u) (2*r))
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change (factorGraph Φ).Reachable _ _ ∧ (factorGraph Φ).dist _ _ ≤ 2*r
    refine ⟨(p.takeUntil _ hv').reachable, ?_⟩
    exact le_trans (SimpleGraph.dist_le (p.takeUntil _ hv')) (le_trans (p.length_takeUntil_le_length hv') plen)
  have hlen : p.reverse.length ≤ 2*r := by simpa using plen
  obtain ⟨v,hv,hc⟩ := audit_clause_walk_neighbor Φ D r p.reverse hg hlen
  exact Finset.mem_biUnion.mpr ⟨v,hv,hc⟩


lemma audit_variable_ball_card {n : ℕ} (Φ : GFormula (Fin n)) (k D r : ℕ)
    (hwidth : ∀ c : Fin Φ.length, (vbl (Φ.get c)).card ≤ k)
    (root : Fin n) (hdeg : ∀ v ∈ ballVars Φ root r, degree Φ v ≤ D) :
    (ballVars Φ root r).card ≤ ∑ h ∈ Finset.range (r+1), (D*k)^h := by
  calc
    _ ≤ (goodVariableReach Φ D root r).card := by
      apply Finset.card_le_card
      intro v hv
      exact (audit_ball_good_reach Φ D r root v hdeg hv).1
    _ ≤ _ := audit_good_variable_reach_card Φ D k hwidth root r

lemma audit_clause_ball_card {n : ℕ} (Φ : GFormula (Fin n)) (k D r : ℕ) (hr : 1 ≤ r)
    (hwidth : ∀ c : Fin Φ.length, (vbl (Φ.get c)).card ≤ k)
    (root : Fin n) (hdeg : ∀ v ∈ ballVars Φ root r, degree Φ v ≤ D) :
    (ballIdx Φ root r).card ≤ D * ∑ h ∈ Finset.range r, (D*k)^h := by
  have hinc : ∀ v : Fin n, (goodIncidentClauses Φ D v).card ≤ D := by
    intro v
    unfold goodIncidentClauses
    by_cases h : degree Φ v ≤ D
    · simp only [h, if_true]
      convert h using 1
      unfold degree
      congr 1
      ext c
      simp [vbl]
    · simp [h]
  have hbase : (goodVariableReach Φ D root (r-1)).card ≤
      ∑ h ∈ Finset.range r, (D*k)^h := by
    have h := audit_good_variable_reach_card Φ D k hwidth root (r-1)
    have he : r-1+1 = r := by omega
    simpa [he] using h
  calc
    _ ≤ ((goodVariableReach Φ D root (r-1)).biUnion (goodIncidentClauses Φ D)).card :=
      Finset.card_le_card (audit_ball_clause_incidence Φ D r root hdeg)
    _ ≤ ∑ v ∈ goodVariableReach Φ D root (r-1), (goodIncidentClauses Φ D v).card := Finset.card_biUnion_le
    _ ≤ (goodVariableReach Φ D root (r-1)).card * D := by
      simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul (goodVariableReach Φ D root (r-1))
        (fun v => (goodIncidentClauses Φ D v).card) D (by intro v hv; exact hinc v)
    _ ≤ D * ∑ h ∈ Finset.range r, (D*k)^h := by nlinarith

lemma audit_geometric_sum_le_pow (q r : ℕ) (hq : 2 ≤ q) :
    (∑ i ∈ Finset.range r, q^i) ≤ q^r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have hp : 0 ≤ q^r := Nat.zero_le _
    nlinarith


lemma audit_forward_ball_bound_big {n : ℕ} (Φ : GFormula (Fin n)) (k D r : ℕ)
    (hk : 1 ≤ k) (hr : 1 ≤ r) (hq : 2 ≤ D*k)
    (hwidth : ∀ c : Fin Φ.length, (vbl (Φ.get c)).card ≤ k)
    (root : Fin n) (hdeg : ∀ v ∈ ballVars Φ root r, degree Φ v ≤ D) :
    (ballVars Φ root r).card + (ballIdx Φ root r).card ≤
      ∑ h ∈ Finset.range (r+2), (D*k)^h := by
  have hv := audit_variable_ball_card Φ k D r hwidth root hdeg
  have hc := audit_clause_ball_card Φ k D r hr hwidth root hdeg
  have hg := audit_geometric_sum_le_pow (D*k) r hq
  have hD : D ≤ D*k := by nlinarith
  have hh : D * (∑ h ∈ Finset.range r, (D*k)^h) ≤ (D*k)^(r+1) := by
    rw [pow_succ]
    have h := Nat.mul_le_mul_right ((D*k)^r) hD
    calc
      D * (∑ h ∈ Finset.range r, (D*k)^h) ≤ D * (D*k)^r := Nat.mul_le_mul_left D hg
      _ ≤ (D*k)^r * (D*k) := by simpa [Nat.mul_comm] using h
  rw [Finset.sum_range_succ]
  omega


lemma audit_unary_reach_singleton {n : ℕ} (Φ : GFormula (Fin n)) (D r : ℕ)
    (hwidth : ∀ c : Fin Φ.length, (vbl (Φ.get c)).card ≤ 1) (root : Fin n) :
    goodVariableReach Φ D root r ⊆ {root} := by
  let N := fun v => (goodIncidentClauses Φ D v).biUnion (fun c => vbl (Φ.get c))
  have hn : ∀ v : Fin n, N v ⊆ {v} := by
    intro v x hx
    obtain ⟨c,hc,hx⟩ := Finset.mem_biUnion.mp hx
    have hv : v ∈ vbl (Φ.get c) := by
      unfold goodIncidentClauses at hc
      split at hc
      · exact (Finset.mem_filter.mp hc).2
      · simpa using hc
    have e : x = v := Finset.card_le_one_iff.mp (hwidth c) hx hv
    simpa [e]
  change boundedReachBall N root r ⊆ {root}
  induction r with
  | zero => simp [boundedReachBall]
  | succ r ih =>
    intro x hx
    simp only [boundedReachBall, Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion] at hx
    rcases hx with rfl | ⟨v,hv,hvx⟩
    · simp
    · have ev : v = root := by simpa using ih hv
      have ex : x = v := by simpa using hn v hvx
      simpa [ev] using ex

lemma audit_forward_ball_bound_unary {n : ℕ} (Φ : GFormula (Fin n)) (r : ℕ) (hr : 1 ≤ r)
    (hwidth : ∀ c : Fin Φ.length, (vbl (Φ.get c)).card ≤ 1)
    (root : Fin n) (hdeg : ∀ v ∈ ballVars Φ root r, degree Φ v ≤ 1) :
    (ballVars Φ root r).card + (ballIdx Φ root r).card ≤
      ∑ h ∈ Finset.range (r+2), (1:ℕ)^h := by
  have hv : (ballVars Φ root r).card ≤ 1 := by
    calc
      _ ≤ (goodVariableReach Φ 1 root r).card := by
        apply Finset.card_le_card
        intro v hv
        exact (audit_ball_good_reach Φ 1 r root v hdeg hv).1
      _ ≤ ({root} : Finset (Fin n)).card := Finset.card_le_card (audit_unary_reach_singleton Φ 1 r hwidth root)
      _ = 1 := Finset.card_singleton root
  have hroot : root ∈ ballVars Φ root r := by
    change root ∈ Finset.univ.filter (fun u => withinDist Φ (Sum.inl root) (Sum.inl u) (2*r))
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    exact ⟨SimpleGraph.Reachable.refl _, by simp⟩
  have hc : (ballIdx Φ root r).card ≤ 1 := by
    have hin : ballIdx Φ root r ⊆ goodIncidentClauses Φ 1 root := by
      intro c hc
      obtain ⟨v,hv,hcv⟩ := Finset.mem_biUnion.mp (audit_ball_clause_incidence Φ 1 r root hdeg hc)
      have ev : v = root := by simpa using (audit_unary_reach_singleton Φ 1 (r-1) hwidth root) hv
      simpa [ev] using hcv
    calc
      _ ≤ (goodIncidentClauses Φ 1 root).card := Finset.card_le_card hin
      _ ≤ 1 := by
        unfold goodIncidentClauses
        have hd := hdeg root hroot
        simp only [hd, if_true]
        convert hd using 1
        unfold degree
        congr 1
        ext c
        simp [vbl]
  have ht : (ballVars Φ root r).card + (ballIdx Φ root r).card ≤ r+2 := by omega
  simpa using ht

/-- The reverse neighborhood bound in Equation (2.1), with no tree assumption. -/
theorem audit_locally_bounded_reverse_card {n : ℕ} (Φ : GFormula (Fin n))
    (k r D : ℕ) (hwidth : ∀ c : Fin Φ.length, (vbl (Φ.get c)).card ≤ k) (u : Fin n) :
    (Finset.univ.filter fun v : Fin n => LocallyTree Φ v r D ∧ u ∈ ballVars Φ v r).card ≤
      ∑ h ∈ Finset.range (r + 1), (k*D)^h := by
  calc
    _ ≤ (goodVariableReach Φ D u r).card := by
      apply Finset.card_le_card
      intro v hv
      have hv' : LocallyTree Φ v r D ∧ u ∈ ballVars Φ v r := (Finset.mem_filter.mp hv).2
      exact (audit_ball_good_reach Φ D r v u hv'.1.2 hv'.2).2
    _ ≤ ∑ h ∈ Finset.range (r + 1), (D*k)^h := audit_good_variable_reach_card Φ D k hwidth u r
    _ = ∑ h ∈ Finset.range (r + 1), (k*D)^h := by rw [Nat.mul_comm D k]


/-- Both metric-ball bounds in Equation (2.1) of Lemma 2.7. -/
theorem audit_lemma_2_7_ball_bounds {n : ℕ} (Φ : GFormula (Fin n)) (k r D : ℕ)
    (hk : 1 ≤ k) (hr : 1 ≤ r) (hD : 1 ≤ D)
    (hwidth : ∀ c : Fin Φ.length, (vbl (Φ.get c)).card ≤ k) :
    (∀ v, LocallyTree Φ v r D →
      (ballVars Φ v r).card + (ballIdx Φ v r).card ≤
        ∑ h ∈ Finset.range (r + 2), (k * D)^h) ∧
    (∀ u, (Finset.univ.filter fun v : Fin n =>
      LocallyTree Φ v r D ∧ u ∈ ballVars Φ v r).card ≤
        ∑ h ∈ Finset.range (r + 2), (k * D)^h) := by
  constructor
  · intro v hv
    by_cases hbig : 2 ≤ D*k
    · simpa [Nat.mul_comm] using audit_forward_ball_bound_big Φ k D r hk hr hbig hwidth v hv.2
    · have hq : D*k = 1 := by nlinarith
      have hd : D = 1 := by nlinarith
      have hkk : k = 1 := by nlinarith
      subst D
      subst k
      simpa using audit_forward_ball_bound_unary Φ r hr hwidth v hv.2
  · intro u
    calc
      _ ≤ ∑ h ∈ Finset.range (r+1), (k*D)^h := audit_locally_bounded_reverse_card Φ k r D hwidth u
      _ ≤ ∑ h ∈ Finset.range (r+2), (k*D)^h := Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))

end KSATSingleFlip.Connect

open KSATSingleFlip.Connect
theorem solution {n : ℕ} (Φ : GFormula (Fin n)) (k r D : ℕ)
    (hk : 1 ≤ k) (hr : 1 ≤ r) (hD : 1 ≤ D)
    (hwidth : ∀ c : Fin Φ.length, (vbl (Φ.get c)).card ≤ k) :
    (∀ v, LocallyTree Φ v r D →
      (ballVars Φ v r).card + (ballIdx Φ v r).card ≤
        ∑ h ∈ Finset.range (r + 2), (k * D)^h) ∧
    (∀ u, (Finset.univ.filter fun v : Fin n =>
      LocallyTree Φ v r D ∧ u ∈ ballVars Φ v r).card ≤
        ∑ h ∈ Finset.range (r + 2), (k * D)^h) := by
  exact audit_lemma_2_7_ball_bounds Φ k r D hk hr hD hwidth

#print axioms solution
