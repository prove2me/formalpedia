-- Prove2me | solution 1 for KSATSingleFlip.Connect.lemma_2_7_changed_ball_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:56:54.73501+00:00
-- url     : https://prove2.me/submissions/82bd1336-2c37-489c-b6c0-4e373fdc5302

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

open KSATSingleFlip.Connect
theorem solution {n : ℕ} (Φ : GFormula (Fin n))
    (C : GClause (Fin n)) (r D : ℕ) :
    ∀ v : Fin n, trimmedBall Φ v r D ≠ trimmedBall (Φ ++ [C]) v r D →
      ∃ u ∈ vbl C,
        (LocallyTree Φ v r D ∧ u ∈ ballVars Φ v r) ∨
        (LocallyTree (Φ ++ [C]) v r D ∧ u ∈ ballVars (Φ ++ [C]) v r) := by
  exact audit_lemma_2_7_changed_ball_endpoint Φ C r D

#print axioms solution
