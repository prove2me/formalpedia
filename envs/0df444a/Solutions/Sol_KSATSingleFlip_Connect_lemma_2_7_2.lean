-- Prove2me | solution 2 for KSATSingleFlip.Connect.lemma_2_7
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:57:40.581206+00:00
-- url     : https://prove2.me/submissions/ee85d42b-c4d6-4423-8979-341c344c074f

import Definitions.Def_KSATSingleFlip_Connect_GoodReach
import Definitions.Def_KSATSingleFlip_Connect_TrimmedBall

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

open scoped Classical BigOperators
namespace KSATSingleFlip.Connect

lemma audit_adj_var_clause {n : ℕ} (Φ : GFormula (Fin n)) (v : Fin n) (c : Fin Φ.length) :
    (factorGraph Φ).Adj (Sum.inl v) (Sum.inr c) ↔ v ∈ vbl (Φ.get c) := by
  simp [factorGraph, SimpleGraph.fromRel_adj, vbl]

def audit_oldNode {n : ℕ} (Φ : GFormula (Fin n)) (C : GClause (Fin n)) :
    (Fin n ⊕ Fin Φ.length) → (Fin n ⊕ Fin (Φ ++ [C]).length) :=
  Sum.map id (Fin.castLE (by simp))

lemma audit_get_append {n : ℕ} (Φ : GFormula (Fin n)) (C : GClause (Fin n)) (c : Fin Φ.length) :
    (Φ ++ [C]).get (Fin.castLE (by simp) c) = Φ.get c := by
  simp [List.get_eq_getElem]

lemma audit_oldNode_inj {n : ℕ} (Φ : GFormula (Fin n)) (C : GClause (Fin n)) :
    Function.Injective (audit_oldNode Φ C) := by
  intro x y h
  cases x <;> cases y <;> simp_all [audit_oldNode, Fin.ext_iff]

def audit_oldHom {n : ℕ} (Φ : GFormula (Fin n)) (C : GClause (Fin n)) :
    factorGraph Φ →g factorGraph (Φ ++ [C]) where
  toFun := audit_oldNode Φ C
  map_rel' := by
    intro x y h
    simp only [factorGraph, SimpleGraph.fromRel_adj] at h ⊢
    refine ⟨fun e => h.1 (audit_oldNode_inj Φ C e), ?_⟩
    rcases h.2 with hxy | hyx
    · left
      obtain ⟨v,c,rfl,rfl,hc⟩ := hxy
      exact ⟨v, Fin.castLE (by simp) c, rfl, rfl, by simpa [audit_get_append] using hc⟩
    · right
      obtain ⟨v,c,rfl,rfl,hc⟩ := hyx
      exact ⟨v, Fin.castLE (by simp) c, rfl, rfl, by simpa [audit_get_append] using hc⟩


lemma audit_oldNode_adj_iff {n : ℕ} (Φ : GFormula (Fin n)) (C : GClause (Fin n))
    (x y : Fin n ⊕ Fin Φ.length) :
    (factorGraph (Φ ++ [C])).Adj (audit_oldNode Φ C x) (audit_oldNode Φ C y) ↔
      (factorGraph Φ).Adj x y := by
  cases x <;> cases y <;> simp [audit_oldNode, factorGraph, SimpleGraph.fromRel_adj, audit_get_append]


/-- A walk on old nodes of the enlarged factor graph lifts to the old graph. -/
lemma audit_lift_old_walk {n : ℕ} (Φ : GFormula (Fin n)) (C : GClause (Fin n))
    {a b : Fin n ⊕ Fin (Φ ++ [C]).length} (p : (factorGraph (Φ ++ [C])).Walk a b)
    (hs : ∀ z ∈ p.support, ∃ x, audit_oldNode Φ C x = z) :
    ∃ x y, audit_oldNode Φ C x = a ∧ audit_oldNode Φ C y = b ∧
      ∃ q : (factorGraph Φ).Walk x y, q.length = p.length := by
  induction p with
  | @nil a =>
    obtain ⟨x,hx⟩ := hs a (by simp)
    exact ⟨x,x,hx,hx,SimpleGraph.Walk.nil,rfl⟩
  | @cons a b c h p ih =>
    obtain ⟨x,hx⟩ := hs a (by simp)
    have htail : ∀ z ∈ p.support, ∃ x, audit_oldNode Φ C x = z := by
      intro z hz
      exact hs z (by simp [hz])
    obtain ⟨y,z,hy,hz,q,hq⟩ := ih htail
    have hadj : (factorGraph Φ).Adj x y := by
      apply (audit_oldNode_adj_iff Φ C x y).mp
      simpa [hx,hy] using h
    exact ⟨x,z,hx,hz,q.cons hadj,by simpa [hq]⟩


def audit_newClause {n : ℕ} (Φ : GFormula (Fin n)) (C : GClause (Fin n)) : Fin (Φ ++ [C]).length :=
  ⟨Φ.length, by simp⟩

lemma audit_get_newClause {n : ℕ} (Φ : GFormula (Fin n)) (C : GClause (Fin n)) :
    (Φ ++ [C]).get (audit_newClause Φ C) = C := by
  simp [audit_newClause, List.get_eq_getElem]

lemma audit_old_or_new {n : ℕ} (Φ : GFormula (Fin n)) (C : GClause (Fin n))
    (z : Fin n ⊕ Fin (Φ ++ [C]).length) :
    (∃ x, audit_oldNode Φ C x = z) ∨ z = Sum.inr (audit_newClause Φ C) := by
  cases z with
  | inl v => exact Or.inl ⟨Sum.inl v, rfl⟩
  | inr c =>
    by_cases h : c.val < Φ.length
    · left
      refine ⟨Sum.inr ⟨c.val,h⟩, ?_⟩
      simp [audit_oldNode, Fin.ext_iff]
    · right
      have he : c.val = Φ.length := by have hc := c.isLt; simp at hc; omega
      congr 1
      apply Fin.ext
      simpa [audit_newClause] using he

lemma audit_short_walk_old_nodes {n : ℕ} (Φ : GFormula (Fin n)) (C : GClause (Fin n))
    (root : Fin n) (r : ℕ) {b} (p : (factorGraph (Φ ++ [C])).Walk (Sum.inl root) b)
    (hlen : p.length ≤ 2*r)
    (hno : Disjoint (vbl C) (ballVars (Φ ++ [C]) root r)) :
    ∀ z ∈ p.support, ∃ x, audit_oldNode Φ C x = z := by
  intro z hz
  rcases audit_old_or_new Φ C z with hold | hnew
  · exact hold
  · subst z
    let q := p.takeUntil (Sum.inr (audit_newClause Φ C)) hz
    have hq : q.length ≤ 2*r := le_trans (p.length_takeUntil_le_length hz) hlen
    have hqr : q.reverse.length ≤ 2*r := by simpa using hq
    generalize he : q.reverse = qr at *
    cases qr with
    | @cons a mid b h qr =>
      cases mid with
      | inr c =>
        have hadj := h
        simp [factorGraph, SimpleGraph.fromRel_adj] at hadj
      | inl u =>
        have hu : u ∈ vbl C := by
          have hadj := h.symm
          rw [audit_adj_var_clause] at hadj
          change u ∈ vbl ((Φ ++ [C]).get (audit_newClause Φ C)) at hadj
          rw [audit_get_newClause] at hadj
          exact hadj
        have hball : u ∈ ballVars (Φ ++ [C]) root r := by
          change u ∈ Finset.univ.filter (fun v => withinDist (Φ ++ [C]) (Sum.inl root) (Sum.inl v) (2*r))
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          have hqrl : qr.length ≤ 2*r := by simp at hqr; omega
          exact ⟨qr.reverse.reachable, le_trans (SimpleGraph.dist_le qr.reverse) (by simpa using hqrl)⟩
        exact (Finset.disjoint_left.mp hno) hu hball |>.elim

theorem audit_append_ballVars_mono {n : ℕ} (Φ : GFormula (Fin n)) (C : GClause (Fin n))
    (v : Fin n) (r : ℕ) : ballVars Φ v r ⊆ ballVars (Φ ++ [C]) v r := by
  intro u hu
  have hdist : withinDist Φ (Sum.inl v) (Sum.inl u) (2*r) := by simpa [ballVars] using hu
  obtain ⟨p,hp⟩ := hdist.1.exists_walk_length_eq_dist
  have hlen : p.length ≤ 2*r := by simpa [hp] using hdist.2
  let p' := p.map (audit_oldHom Φ C)
  have h' : withinDist (Φ ++ [C]) (Sum.inl v) (Sum.inl u) (2*r) := by
    refine ⟨p'.reachable, ?_⟩
    exact le_trans (SimpleGraph.dist_le p') (by simpa [p'] using hlen)
  simpa [ballVars] using h'

/-- If the inserted clause has no variable in the new ball, its variable set is unchanged. -/
theorem audit_append_ballVars_eq_of_disjoint {n : ℕ} (Φ : GFormula (Fin n))
    (C : GClause (Fin n)) (root : Fin n) (r : ℕ)
    (hno : Disjoint (vbl C) (ballVars (Φ ++ [C]) root r)) :
    ballVars (Φ ++ [C]) root r = ballVars Φ root r := by
  apply Finset.Subset.antisymm
  · intro u hu
    have hdist : withinDist (Φ ++ [C]) (Sum.inl root) (Sum.inl u) (2*r) := by simpa [ballVars] using hu
    obtain ⟨p,hp⟩ := hdist.1.exists_walk_length_eq_dist
    have hlen : p.length ≤ 2*r := by simpa [hp] using hdist.2
    have hs := audit_short_walk_old_nodes Φ C root r p hlen hno
    obtain ⟨x,y,hx,hy,q,hq⟩ := audit_lift_old_walk Φ C p hs
    have hx' : x = Sum.inl root := audit_oldNode_inj Φ C (by simpa [audit_oldNode] using hx)
    have hy' : y = Sum.inl u := audit_oldNode_inj Φ C (by simpa [audit_oldNode] using hy)
    subst x
    subst y
    have hdist' : withinDist Φ (Sum.inl root) (Sum.inl u) (2*r) := by
      refine ⟨q.reachable, le_trans (SimpleGraph.dist_le q) ?_⟩
      omega
    simpa [ballVars] using hdist'
  · exact audit_append_ballVars_mono Φ C root r


lemma audit_ballIdx_old_iff {n : ℕ} (Φ : GFormula (Fin n)) (C : GClause (Fin n))
    (root : Fin n) (r : ℕ) (hno : Disjoint (vbl C) (ballVars (Φ ++ [C]) root r))
    (c : Fin Φ.length) : c ∈ ballIdx Φ root r ↔
      Fin.castLE (by simp) c ∈ ballIdx (Φ ++ [C]) root r := by
  constructor
  · intro hc
    have hd : withinDist Φ (Sum.inl root) (Sum.inr c) (2*r) := by simpa [ballIdx] using hc
    obtain ⟨p,hp⟩ := hd.1.exists_walk_length_eq_dist
    have hlen : p.length ≤ 2*r := by simpa [hp] using hd.2
    let q := p.map (audit_oldHom Φ C)
    have hd' : withinDist (Φ ++ [C]) (Sum.inl root) (Sum.inr (Fin.castLE (by simp) c)) (2*r) := by
      refine ⟨q.reachable, le_trans (SimpleGraph.dist_le q) ?_⟩
      simpa [q] using hlen
    simpa [ballIdx] using hd'
  · intro hc
    have hd : withinDist (Φ ++ [C]) (Sum.inl root) (Sum.inr (Fin.castLE (by simp) c)) (2*r) := by simpa [ballIdx] using hc
    obtain ⟨p,hp⟩ := hd.1.exists_walk_length_eq_dist
    have hlen : p.length ≤ 2*r := by simpa [hp] using hd.2
    have hs := audit_short_walk_old_nodes Φ C root r p hlen hno
    obtain ⟨x,y,hx,hy,q,hq⟩ := audit_lift_old_walk Φ C p hs
    have hx' : x = Sum.inl root := audit_oldNode_inj Φ C (by simpa [audit_oldNode] using hx)
    have hy' : y = Sum.inr c := audit_oldNode_inj Φ C (by simpa [audit_oldNode] using hy)
    subst x
    subst y
    have hd' : withinDist Φ (Sum.inl root) (Sum.inr c) (2*r) := by
      refine ⟨q.reachable, le_trans (SimpleGraph.dist_le q) ?_⟩
      omega
    simpa [ballIdx] using hd'

lemma audit_ballIdx_new_old {n : ℕ} (Φ : GFormula (Fin n)) (C : GClause (Fin n))
    (root : Fin n) (r : ℕ) (hno : Disjoint (vbl C) (ballVars (Φ ++ [C]) root r))
    (c : Fin (Φ ++ [C]).length) (hc : c ∈ ballIdx (Φ ++ [C]) root r) :
    ∃ d : Fin Φ.length, Fin.castLE (by simp) d = c := by
  have hd : withinDist (Φ ++ [C]) (Sum.inl root) (Sum.inr c) (2*r) := by simpa [ballIdx] using hc
  obtain ⟨p,hp⟩ := hd.1.exists_walk_length_eq_dist
  have hlen : p.length ≤ 2*r := by simpa [hp] using hd.2
  have hs := audit_short_walk_old_nodes Φ C root r p hlen hno
  obtain ⟨x,hx⟩ := hs (Sum.inr c) (by simp)
  cases x with
  | inl v => simp [audit_oldNode] at hx
  | inr d =>
    refine ⟨d, ?_⟩
    simpa [audit_oldNode] using hx


lemma audit_ballClauseLabels_eq {n : ℕ} (Φ : GFormula (Fin n)) (C : GClause (Fin n))
    (root : Fin n) (r : ℕ) (hno : Disjoint (vbl C) (ballVars (Φ ++ [C]) root r)) :
    ballClauseLabels (Φ ++ [C]) root r = ballClauseLabels Φ root r := by
  unfold ballClauseLabels
  ext j
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨c,hc,hj⟩
    obtain ⟨d,hd⟩ := audit_ballIdx_new_old Φ C root r hno c hc
    refine ⟨d, (audit_ballIdx_old_iff Φ C root r hno d).mpr ?_, ?_⟩
    · simpa [hd] using hc
    · simpa [← hd] using hj
  · rintro ⟨c,hc,hj⟩
    refine ⟨Fin.castLE (by simp) c, (audit_ballIdx_old_iff Φ C root r hno c).mp hc, ?_⟩
    simpa using hj


lemma audit_zipIdx_finRange {α : Type} (xs : List α) :
    xs.zipIdx = (List.finRange xs.length).map (fun j => (xs.get j, j.val)) := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp [List.get_eq_getElem, List.getElem_zipIdx]

lemma audit_subF_labels {n : ℕ} (Φ : GFormula (Fin n)) (I : Finset (Fin Φ.length)) :
    subF Φ I = Φ.zipIdx.filterMap (fun (C,j) => if j ∈ I.image Fin.val then some C else none) := by
  rw [audit_zipIdx_finRange, List.filterMap_map]
  unfold subF
  congr 1
  funext j
  have hh : j.val ∈ I.image Fin.val ↔ j ∈ I := by
    constructor
    · intro h
      obtain ⟨a,ha,he⟩ := Finset.mem_image.mp h
      have : a = j := Fin.ext he
      simpa [this] using ha
    · intro h
      exact Finset.mem_image.mpr ⟨j,h,rfl⟩
  change (if j ∈ I then some (Φ.get j) else none) =
    (if j.val ∈ I.image Fin.val then some (Φ.get j) else none)
  by_cases hj : j ∈ I
  · have hj' : j.val ∈ I.image Fin.val := hh.mpr hj
    simp only [hj, hj', if_true]
  · have hj' : j.val ∉ I.image Fin.val := fun h => hj (hh.mp h)
    simp only [hj, hj', if_false]


lemma audit_newClause_not_ballIdx {n : ℕ} (Φ : GFormula (Fin n)) (C : GClause (Fin n))
    (root : Fin n) (r : ℕ) (hno : Disjoint (vbl C) (ballVars (Φ ++ [C]) root r)) :
    audit_newClause Φ C ∉ ballIdx (Φ ++ [C]) root r := by
  intro hc
  obtain ⟨d,hd⟩ := audit_ballIdx_new_old Φ C root r hno _ hc
  have he := congrArg Fin.val hd
  simp [audit_newClause] at he
  omega


lemma audit_degree_eq_filter {n : ℕ} (Φ : GFormula (Fin n)) (u : Fin n) :
    degree Φ u = (Φ.filter (fun C => (C u).isSome)).length := by
  induction Φ with
  | nil => simp [degree]
  | cons C Φ ih =>
    unfold degree at ih ⊢
    simp only [List.length_cons] at *
    rw [Fin.card_filter_univ_succ]
    simp only [List.get_cons_zero, List.filter_cons, apply_ite, List.length_cons]
    simp [List.get_eq_getElem] at ih ⊢
    rw [ih]
    split_ifs <;> simp_all


/-- Inserting one clause changes exactly the degrees of its variables. -/
theorem audit_degree_append {n : ℕ} (Φ : GFormula (Fin n)) (C : GClause (Fin n)) (u : Fin n) :
    degree (Φ ++ [C]) u = degree Φ u + if u ∈ vbl C then 1 else 0 := by
  simp [audit_degree_eq_filter, vbl, List.filter_append]
  split_ifs <;> simp_all


lemma audit_ballF_eq {n : ℕ} (Φ : GFormula (Fin n)) (C : GClause (Fin n))
    (root : Fin n) (r : ℕ) (hno : Disjoint (vbl C) (ballVars (Φ ++ [C]) root r)) :
    ballF (Φ ++ [C]) root r = ballF Φ root r := by
  unfold ballF
  rw [audit_subF_labels, audit_subF_labels]
  have he := audit_ballClauseLabels_eq Φ C root r hno
  unfold ballClauseLabels at he
  rw [he]
  have hn : Φ.length ∉ (ballIdx Φ root r).image Fin.val := by
    intro hn
    obtain ⟨j,hj,heq⟩ := Finset.mem_image.mp hn
    have := j.isLt
    omega
  have hn' : ∀ x ∈ ballIdx Φ root r, x.val ≠ Φ.length := by
    intro x hx
    exact Nat.ne_of_lt x.isLt
  simp [List.zipIdx_append]
  exact hn' 


/-- If no inserted-clause variable is in the old ball, none enters the new ball. -/
lemma audit_disjoint_old_implies_new {n : ℕ} (Φ : GFormula (Fin n)) (C : GClause (Fin n))
    (root : Fin n) (r : ℕ) (hno : Disjoint (vbl C) (ballVars Φ root r)) :
    Disjoint (vbl C) (ballVars (Φ ++ [C]) root r) := by
  letI : BEq (Fin n ⊕ Fin (Φ ++ [C]).length) := instBEqOfDecidableEq
  letI : LawfulBEq (Fin n ⊕ Fin (Φ ++ [C]).length) := {
    rfl := by intro a; simp [BEq.beq, instBEqOfDecidableEq]
    eq_of_beq := by intro a b h; exact of_decide_eq_true h }
  apply Finset.disjoint_left.mpr
  intro u hu huball
  have hd : withinDist (Φ ++ [C]) (Sum.inl root) (Sum.inl u) (2*r) := by simpa [ballVars] using huball
  obtain ⟨p,hp⟩ := hd.1.exists_walk_length_eq_dist
  have hlen : p.length ≤ 2*r := by simpa [hp] using hd.2
  by_cases hnew : Sum.inr (audit_newClause Φ C) ∈ p.support
  · let q := p.takeUntil (Sum.inr (audit_newClause Φ C)) hnew
    have hq : q.length ≤ 2*r := le_trans (p.length_takeUntil_le_length hnew) hlen
    have hcount : q.reverse.support.count (Sum.inr (audit_newClause Φ C)) = 1 := by
      simpa only [SimpleGraph.Walk.support_reverse, List.count_reverse, q] using p.count_support_takeUntil_eq_one hnew
    generalize he : q.reverse = qr at *
    cases qr with
    | @cons a mid b h qr =>
      cases mid with
      | inr c =>
        have hh := h
        simp [factorGraph, SimpleGraph.fromRel_adj] at hh
      | inl v =>
        have hv : v ∈ vbl C := by
          have hh := h.symm
          rw [audit_adj_var_clause] at hh
          change v ∈ vbl ((Φ ++ [C]).get (audit_newClause Φ C)) at hh
          rwa [audit_get_newClause] at hh
        have hqold : Sum.inr (audit_newClause Φ C) ∉ qr.support := by
          simp only [SimpleGraph.Walk.support_cons, List.count_cons, ↓reduceIte] at hcount
          have hc0 : qr.support.count (Sum.inr (audit_newClause Φ C)) = 0 := by
            simp only [beq_self_eq_true, if_true] at hcount
            omega
          exact List.count_eq_zero.mp hc0
        have hs : ∀ z ∈ qr.reverse.support, ∃ x, audit_oldNode Φ C x = z := by
          intro z hz
          rcases audit_old_or_new Φ C z with hold | hnew
          · exact hold
          · subst z
            have : Sum.inr (audit_newClause Φ C) ∈ qr.support := by simpa using hz
            exact (hqold this).elim
        obtain ⟨x,y,hx,hy,w,hw⟩ := audit_lift_old_walk Φ C qr.reverse hs
        have hx' : x = Sum.inl root := audit_oldNode_inj Φ C (by simpa [audit_oldNode] using hx)
        have hy' : y = Sum.inl v := audit_oldNode_inj Φ C (by simpa [audit_oldNode] using hy)
        subst x
        subst y
        have hvball : v ∈ ballVars Φ root r := by
          change v ∈ Finset.univ.filter (fun x => withinDist Φ (Sum.inl root) (Sum.inl x) (2*r))
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, w.reachable, le_trans (SimpleGraph.dist_le w) ?_⟩
          simp only [SimpleGraph.Walk.length_reverse] at hw
          have hq' : qr.length + 1 ≤ 2*r := by
            have hh := hq
            rw [← SimpleGraph.Walk.length_reverse q] at hh
            rw [he] at hh
            simpa using hh
          omega
        exact (Finset.disjoint_left.mp hno) hv hvball
  · have hs : ∀ z ∈ p.support, ∃ x, audit_oldNode Φ C x = z := by
      intro z hz
      rcases audit_old_or_new Φ C z with hold | he
      · exact hold
      · subst z
        exact (hnew hz).elim
    obtain ⟨x,y,hx,hy,w,hw⟩ := audit_lift_old_walk Φ C p hs
    have hx' : x = Sum.inl root := audit_oldNode_inj Φ C (by simpa [audit_oldNode] using hx)
    have hy' : y = Sum.inl u := audit_oldNode_inj Φ C (by simpa [audit_oldNode] using hy)
    subst x
    subst y
    have huold : u ∈ ballVars Φ root r := by
      change u ∈ Finset.univ.filter (fun x => withinDist Φ (Sum.inl root) (Sum.inl x) (2*r))
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, w.reachable, le_trans (SimpleGraph.dist_le w) ?_⟩
      omega
    exact (Finset.disjoint_left.mp hno) hu huold


lemma audit_trimmedBall_eq_of_disjoint {n : ℕ} (Φ : GFormula (Fin n))
    (C : GClause (Fin n)) (root : Fin n) (r D : ℕ)
    (hno : Disjoint (vbl C) (ballVars (Φ ++ [C]) root r)) :
    trimmedBall (Φ ++ [C]) root r D = trimmedBall Φ root r D := by
  have hv := audit_append_ballVars_eq_of_disjoint Φ C root r hno
  have hc := audit_ballClauseLabels_eq Φ C root r hno
  have hf := audit_ballF_eq Φ C root r hno
  have hdegree : ∀ v ∈ ballVars Φ root r, degree (Φ ++ [C]) v = degree Φ v := by
    intro v hvmem
    have hn : v ∉ vbl C := by
      intro hvc
      apply (Finset.disjoint_left.mp hno) hvc
      rw [hv]
      exact hvmem
    simp only [audit_degree_append, hn, if_false, Nat.add_zero]
  have hl : LocallyTree (Φ ++ [C]) root r D ↔ LocallyTree Φ root r D := by
    unfold LocallyTree BallIsTree
    rw [hf, hv]
    constructor
    · rintro ⟨ht,hd⟩
      refine ⟨ht, ?_⟩
      intro v hvmem
      have hh := hd v hvmem
      rw [hdegree v hvmem] at hh
      exact hh
    · rintro ⟨ht,hd⟩
      refine ⟨ht, ?_⟩
      intro v hvmem
      rw [hdegree v hvmem]
      exact hd v hvmem
  unfold trimmedBall
  by_cases h : LocallyTree Φ root r D
  · have h' := hl.mpr h
    simp [h, h', hv, hc, hf]
  · have h' : ¬ LocallyTree (Φ ++ [C]) root r D := fun h' => h (hl.mp h')
    simp [h, h']

/-- A changed trimmed ball sees a variable of the inserted clause. -/
theorem audit_lemma_2_7_changed_ball_endpoint {n : ℕ} (Φ : GFormula (Fin n))
    (C : GClause (Fin n)) (r D : ℕ) :
    ∀ v : Fin n, trimmedBall Φ v r D ≠ trimmedBall (Φ ++ [C]) v r D →
      ∃ u ∈ vbl C,
        (LocallyTree Φ v r D ∧ u ∈ ballVars Φ v r) ∨
        (LocallyTree (Φ ++ [C]) v r D ∧ u ∈ ballVars (Φ ++ [C]) v r) := by
  intro v hchange
  by_cases hnew : LocallyTree (Φ ++ [C]) v r D
  · by_contra hnone
    have hd : Disjoint (vbl C) (ballVars (Φ ++ [C]) v r) := by
      apply Finset.disjoint_left.mpr
      intro u hu hv
      apply hnone
      exact ⟨u, hu, Or.inr ⟨hnew,hv⟩⟩
    exact hchange (audit_trimmedBall_eq_of_disjoint Φ C v r D hd).symm
  · have hold : LocallyTree Φ v r D := by
      by_contra h
      apply hchange
      simp [trimmedBall, h, hnew]
    by_contra hnone
    have hdold : Disjoint (vbl C) (ballVars Φ v r) := by
      apply Finset.disjoint_left.mpr
      intro u hu hv
      apply hnone
      exact ⟨u, hu, Or.inl ⟨hold,hv⟩⟩
    have hdnew := audit_disjoint_old_implies_new Φ C v r hdold
    exact hchange (audit_trimmedBall_eq_of_disjoint Φ C v r D hdnew).symm

end KSATSingleFlip.Connect


open scoped Classical BigOperators
namespace KSATSingleFlip.Connect

/-- If each changed root lies in an old or new family around one endpoint,
and each such family has at most M roots, there are at most 2kM changed roots. -/
theorem audit_changed_union_bound {V : Type} [DecidableEq V]
    (S changed : Finset V) (old new : V → Finset V) (k M : ℕ)
    (hS : S.card ≤ k)
    (hold : ∀ u ∈ S, (old u).card ≤ M)
    (hnew : ∀ u ∈ S, (new u).card ≤ M)
    (hcover : ∀ v ∈ changed, ∃ u ∈ S, v ∈ old u ∨ v ∈ new u) :
    changed.card ≤ 2 * k * M := by
  let U := S.biUnion fun u => old u ∪ new u
  have hsub : changed ⊆ U := by
    intro v hv
    obtain ⟨u, hu, hmem⟩ := hcover v hv
    exact Finset.mem_biUnion.mpr ⟨u, hu, Finset.mem_union.mpr hmem⟩
  calc
    changed.card ≤ U.card := Finset.card_le_card hsub
    _ ≤ ∑ u ∈ S, (old u ∪ new u).card := Finset.card_biUnion_le
    _ ≤ S.card * (2 * M) := by
      simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul S (fun u => (old u ∪ new u).card) (2*M)
        (by intro u hu; have hc := Finset.card_union_le (old u) (new u); have ho := hold u hu; have hn := hnew u hu; omega)
    _ ≤ 2 * k * M := by nlinarith

end KSATSingleFlip.Connect

open KSATSingleFlip.Connect

theorem audit_lemma_2_7_changed_balls {n : ℕ} (Φ : GFormula (Fin n)) (C : GClause (Fin n)) (k r D : ℕ)
    (hk : 1 ≤ k) (hr : 1 ≤ r) (hD : 1 ≤ D)
    (hwidth : ∀ c : Fin Φ.length, (vbl (Φ.get c)).card ≤ k) (hC : (vbl C).card ≤ k) :
    (Finset.univ.filter fun v : Fin n =>
      trimmedBall Φ v r D ≠ trimmedBall (Φ ++ [C]) v r D).card ≤
        2 * k * ∑ h ∈ Finset.range (r + 2), (k * D)^h := by
  classical
  have hnewwidth : ∀ c : Fin (Φ ++ [C]).length, (vbl ((Φ ++ [C]).get c)).card ≤ k := by
    intro c
    have hm := List.get_mem (Φ ++ [C]) c
    rcases List.mem_append.mp hm with hold | hlast
    · obtain ⟨j, hj⟩ := List.mem_iff_get.mp hold
      rw [← hj]
      exact hwidth j
    · have he : (Φ ++ [C]).get c = C := by simpa using hlast
      rw [he]
      exact hC
  let old : Fin n → Finset (Fin n) := fun u => Finset.univ.filter fun v =>
    LocallyTree Φ v r D ∧ u ∈ ballVars Φ v r
  let new : Fin n → Finset (Fin n) := fun u => Finset.univ.filter fun v =>
    LocallyTree (Φ ++ [C]) v r D ∧ u ∈ ballVars (Φ ++ [C]) v r
  let changed : Finset (Fin n) := Finset.univ.filter fun v =>
    trimmedBall Φ v r D ≠ trimmedBall (Φ ++ [C]) v r D
  let M := ∑ h ∈ Finset.range (r + 2), (k * D)^h
  have hold : ∀ u ∈ vbl C, (old u).card ≤ M := by
    intro u hu
    exact (audit_lemma_2_7_ball_bounds Φ k r D hk hr hD hwidth).2 u
  have hnew : ∀ u ∈ vbl C, (new u).card ≤ M := by
    intro u hu
    exact (audit_lemma_2_7_ball_bounds (Φ ++ [C]) k r D hk hr hD hnewwidth).2 u
  have hcover : ∀ v ∈ changed, ∃ u ∈ vbl C, v ∈ old u ∨ v ∈ new u := by
    intro v hv
    have hv' : trimmedBall Φ v r D ≠ trimmedBall (Φ ++ [C]) v r D := by
      simpa [changed] using hv
    obtain ⟨u, hu, hmem⟩ := audit_lemma_2_7_changed_ball_endpoint Φ C r D v hv'
    refine ⟨u, hu, ?_⟩
    simpa [old, new] using hmem
  exact audit_changed_union_bound (vbl C) changed old new k M hC hold hnew hcover



open scoped Classical BigOperators
namespace KSATSingleFlip.Connect

/-- A sum of [0,1]-valued observables changes by at most the number of
coordinates whose inputs change. -/
theorem audit_changed_coordinate_sum {A B : Type} [Fintype A] (u v : A → B)
    (f : A → B → ℝ) (hf : ∀ a b, 0 ≤ f a b ∧ f a b ≤ 1) :
    |(∑ a, f a (u a)) - ∑ a, f a (v a)| ≤
      ((Finset.univ.filter fun a => u a ≠ v a).card : ℝ) := by
  classical
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ a, (f a (u a) - f a (v a))| ≤ ∑ a, |f a (u a) - f a (v a)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, if u a ≠ v a then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro a ha
      by_cases h : u a = v a
      · simp [h]
      · rw [if_pos h]
        apply abs_le.mpr
        constructor <;> linarith [(hf a (u a)).1, (hf a (u a)).2, (hf a (v a)).1, (hf a (v a)).2]
    _ = _ := by simp [Finset.card_filter]

end KSATSingleFlip.Connect

open KSATSingleFlip.Connect

theorem solution {n : ℕ} (Φ : GFormula (Fin n)) (C : GClause (Fin n)) (k r D : ℕ)
    (hk : 1 ≤ k) (hr : 1 ≤ r) (hD : 1 ≤ D)
    (hwidth : ∀ c : Fin Φ.length, (vbl (Φ.get c)).card ≤ k) (hC : (vbl C).card ≤ k) :
    (∀ v, LocallyTree Φ v r D →
      (ballVars Φ v r).card + (ballIdx Φ v r).card ≤
        ∑ h ∈ Finset.range (r + 2), (k * D)^h) ∧
    (∀ u, (Finset.univ.filter fun v : Fin n =>
      LocallyTree Φ v r D ∧ u ∈ ballVars Φ v r).card ≤
        ∑ h ∈ Finset.range (r + 2), (k * D)^h) ∧
    ((Finset.univ.filter fun v : Fin n =>
      trimmedBall Φ v r D ≠ trimmedBall (Φ ++ [C]) v r D).card ≤
        2 * k * ∑ h ∈ Finset.range (r + 2), (k * D)^h) ∧
    (∀ f : Fin n → Option (Finset (Fin n) × Finset ℕ × GFormula (Fin n)) → ℝ,
      (∀ v b, 0 ≤ f v b ∧ f v b ≤ 1) →
      |(∑ v, f v (trimmedBall Φ v r D)) -
        (∑ v, f v (trimmedBall (Φ ++ [C]) v r D))| ≤
        (2 * k * ∑ h ∈ Finset.range (r + 2), (k * D)^h : ℕ)) := by
  have hballs := audit_lemma_2_7_ball_bounds Φ k r D hk hr hD hwidth
  have hchanged := audit_lemma_2_7_changed_balls Φ C k r D hk hr hD hwidth hC
  refine ⟨hballs.1, hballs.2, hchanged, ?_⟩
  intro f hf
  have hsum := audit_changed_coordinate_sum (fun v => trimmedBall Φ v r D)
    (fun v => trimmedBall (Φ ++ [C]) v r D) f hf
  exact hsum.trans (Nat.cast_le.mpr hchanged)

#print axioms solution
