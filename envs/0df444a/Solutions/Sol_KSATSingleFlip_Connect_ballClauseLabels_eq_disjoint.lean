-- Prove2me | solution 1 for KSATSingleFlip.Connect.ballClauseLabels_eq_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:53:36.388922+00:00
-- url     : https://prove2.me/submissions/841b1c3c-6c21-43f3-b5db-c9cfa1a93395

import Definitions.Def_KSATSingleFlip_Connect_TrimmedBall
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


lemma audit_newClause_not_ballIdx {n : ℕ} (Φ : GFormula (Fin n)) (C : GClause (Fin n))
    (root : Fin n) (r : ℕ) (hno : Disjoint (vbl C) (ballVars (Φ ++ [C]) root r)) :
    audit_newClause Φ C ∉ ballIdx (Φ ++ [C]) root r := by
  intro hc
  obtain ⟨d,hd⟩ := audit_ballIdx_new_old Φ C root r hno _ hc
  have he := congrArg Fin.val hd
  simp [audit_newClause] at he
  omega

end KSATSingleFlip.Connect

open KSATSingleFlip.Connect
theorem solution {n : ℕ} (Φ : GFormula (Fin n)) (C : GClause (Fin n))
    (root : Fin n) (r : ℕ) (hno : Disjoint (vbl C) (ballVars (Φ ++ [C]) root r)) :
    ballClauseLabels (Φ ++ [C]) root r = ballClauseLabels Φ root r := by
  exact audit_ballClauseLabels_eq Φ C root r hno

#print axioms solution
