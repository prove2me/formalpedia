-- Prove2me | solution 1 for MetricGenerators.ConnectedJoin.minimal_realization_unique
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T20:31:09.737666+00:00
-- url     : https://prove2.me/submissions/399557f2-08b2-49eb-99c8-0efa1b6c247d

import Mathlib
import Definitions.Def_MetricGenerators_ConnectedJoin_TreeMetric

open SimpleGraph MetricGenerators.ConnectedJoin

namespace CJUniqueAux

section Tree

variable {α : Type*} [DecidableEq α] {A : SimpleGraph α}

theorem path_length_eq_dist (hA : A.IsTree) {u v : α} (p : A.Walk u v) (hp : p.IsPath) :
    p.length = A.dist u v := by
  obtain ⟨q, hq, hql⟩ := hA.connected.exists_path_of_dist u v
  have := (hA.isAcyclic.subsingleton_path u v).elim ⟨p, hp⟩ ⟨q, hq⟩
  rw [Subtype.mk.injEq] at this; rw [this, hql]

/-- A neighbour that is not farther from `u` is exactly one step closer. -/
theorem closer_succ (hA : A.IsTree) {u w z : α} (hzw : A.Adj z w)
    (h : A.dist u z ≤ A.dist u w) : A.dist u z + 1 = A.dist u w := by
  obtain ⟨q, hq, hql⟩ := hA.connected.exists_path_of_dist u z
  have hwq : w ∉ q.support := by
    intro hw
    have h1 := q.length_takeUntil_lt_length hw hzw.ne.symm
    have h2 := dist_le (q.takeUntil w hw)
    omega
  have hp : (Walk.cons hzw.symm q.reverse).IsPath :=
    hq.reverse.cons (by simpa using hwq)
  have := path_length_eq_dist hA _ hp
  rw [Walk.length_cons, Walk.length_reverse, hql] at this
  rw [this]; exact SimpleGraph.dist_comm

theorem adj_dist (hA : A.IsTree) {u w z : α} (hzw : A.Adj z w) :
    A.dist u z + 1 = A.dist u w ∨ A.dist u w + 1 = A.dist u z := by
  rcases le_total (A.dist u z) (A.dist u w) with h | h
  · exact Or.inl (closer_succ hA hzw h)
  · exact Or.inr (closer_succ hA hzw.symm h)

/-- At most one neighbour of `w` is closer to `u`. -/
theorem closer_unique (hA : A.IsTree) {u w z1 z2 : α} (h1 : A.Adj w z1) (h2 : A.Adj w z2)
    (hd1 : A.dist u z1 < A.dist u w) (hd2 : A.dist u z2 < A.dist u w) : z1 = z2 := by
  have key : ∀ z, A.Adj w z → A.dist u z < A.dist u w →
      ∃ R : A.Walk w u, R.IsPath ∧ R.snd = z := by
    intro z hz hd
    obtain ⟨q, hq, hql⟩ := hA.connected.exists_path_of_dist u z
    have hwq : w ∉ q.support := by
      intro hw
      have := dist_le (q.takeUntil w hw)
      have := q.length_takeUntil_le_length hw
      omega
    exact ⟨Walk.cons hz q.reverse, hq.reverse.cons (by simpa using hwq), by simp⟩
  obtain ⟨R1, hR1, hs1⟩ := key z1 h1 hd1
  obtain ⟨R2, hR2, hs2⟩ := key z2 h2 hd2
  have := (hA.isAcyclic.subsingleton_path w u).elim ⟨R1, hR1⟩ ⟨R2, hR2⟩
  rw [Subtype.mk.injEq] at this
  rw [← hs1, ← hs2, this]

theorem exists_closer (hA : A.IsTree) {u p : α} (hup : u ≠ p) :
    ∃ z, A.Adj u z ∧ A.dist p z + 1 = A.dist p u := by
  obtain ⟨P, hP, hPl⟩ := hA.connected.exists_path_of_dist u p
  have hnil : ¬ P.Nil := fun h => hup h.eq
  refine ⟨P.snd, Walk.adj_snd hnil, ?_⟩
  have h1 := Walk.length_tail_add_one hnil
  have h3 : A.dist p P.snd ≤ P.tail.length := by rw [SimpleGraph.dist_comm]; exact dist_le _
  have h4 : P.length = A.dist p u := by rw [hPl, SimpleGraph.dist_comm]
  rcases adj_dist hA (u := p) (Walk.adj_snd hnil) with h | h <;> omega

theorem support_tail_ne {u v : α} (P : A.Walk u v) (hP : P.IsPath) {x : α}
    (hx : x ∈ P.support.tail) : x ≠ u := by
  intro h
  subst h
  have hnd := hP.support_nodup
  rw [← Walk.cons_tail_support, List.nodup_cons] at hnd
  exact hnd.1 hx

/-- If the branches towards `p` and towards `q` at `v` differ, then `v` is on the `p`–`q`
geodesic. -/
theorem geodesic_of_branches (hA : A.IsTree) {v a b p q : α} (ha : A.Adj v a) (hb : A.Adj v b)
    (hab : a ≠ b) (hpa : A.dist p a < A.dist p v) (hqb : A.dist q b < A.dist q v) :
    A.dist p q = A.dist p v + A.dist q v := by
  obtain ⟨P1, hP1, hP1l⟩ := hA.connected.exists_path_of_dist v p
  obtain ⟨P2, hP2, hP2l⟩ := hA.connected.exists_path_of_dist v q
  have hvp : v ≠ p := by intro h; subst h; simp at hpa
  have hvq : v ≠ q := by intro h; subst h; simp at hqb
  have hn1 : ¬ P1.Nil := fun h => hvp h.eq
  have hn2 : ¬ P2.Nil := fun h => hvq h.eq
  have hs1 : P1.snd = a := by
    apply closer_unique hA (u := p) (Walk.adj_snd hn1) ha _ hpa
    have h1 := Walk.length_tail_add_one hn1
    have h3 : A.dist p P1.snd ≤ P1.tail.length := by rw [SimpleGraph.dist_comm]; exact dist_le _
    have h4 : P1.length = A.dist p v := by rw [hP1l, SimpleGraph.dist_comm]
    omega
  have hs2 : P2.snd = b := by
    apply closer_unique hA (u := q) (Walk.adj_snd hn2) hb _ hqb
    have h1 := Walk.length_tail_add_one hn2
    have h3 : A.dist q P2.snd ≤ P2.tail.length := by rw [SimpleGraph.dist_comm]; exact dist_le _
    have h4 : P2.length = A.dist q v := by rw [hP2l, SimpleGraph.dist_comm]
    omega
  have hW : (P1.reverse.append P2).IsPath := by
    rw [Walk.isPath_def, Walk.support_append, List.nodup_append']
    refine ⟨by rw [Walk.support_reverse]; exact (List.nodup_reverse.2 hP1.support_nodup),
      hP2.support_nodup.sublist (List.tail_sublist _), ?_⟩
    intro x hx1 hx2
    rw [Walk.support_reverse, List.mem_reverse] at hx1
    have hxv : x ≠ v := support_tail_ne P2 hP2 hx2
    have hx2' : x ∈ P2.support := List.mem_of_mem_tail hx2
    have e1 := Walk.snd_takeUntil hxv P1 hx1
    have e2 := Walk.snd_takeUntil hxv P2 hx2'
    have := (hA.isAcyclic.subsingleton_path v x).elim
      ⟨_, hP1.takeUntil hx1⟩ ⟨_, hP2.takeUntil hx2'⟩
    rw [Subtype.mk.injEq] at this
    apply hab
    rw [← hs1, ← hs2, ← e1, ← e2, this]
  have := path_length_eq_dist hA _ hW
  rw [Walk.length_append, Walk.length_reverse, hP1l, hP2l] at this
  rw [← this, SimpleGraph.dist_comm (u := p), SimpleGraph.dist_comm (u := q)]

variable [Fintype α] [DecidableRel A.Adj]

/-- Extension to a leaf: if all leaves lie in `S` and `u ≠ v`, some `w ∈ S` sees `v` on its
geodesic to `u`. -/
theorem extend_to_leaf (hA : A.IsTree) (S : Set α) (hS : ∀ w, A.degree w = 1 → w ∈ S)
    {u v : α} (huv : u ≠ v) : ∃ w ∈ S, A.dist u w = A.dist u v + A.dist v w := by
  classical
  have hconn := hA.connected
  obtain ⟨w, hwS, hwmax⟩ := Finset.exists_max_image
    (Finset.univ.filter (fun w => A.dist u w = A.dist u v + A.dist v w)) (fun w => A.dist u w)
    ⟨v, by simp⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hwS hwmax
  refine ⟨w, hS w ?_, hwS⟩
  have hpos : 0 < A.dist u v := hconn.pos_dist_of_ne huv
  have hwu : w ≠ u := by intro h; subst h; simp at hwS; omega
  obtain ⟨z0, hz0, hz0d⟩ := exists_closer hA hwu
  by_contra hdeg
  have hdeg2 : 1 < A.degree w := by
    have : 0 < A.degree w := by
      rw [← card_neighborFinset_eq_degree]
      exact Finset.card_pos.2 ⟨z0, by simpa using hz0⟩
    omega
  rw [← card_neighborFinset_eq_degree, Finset.one_lt_card] at hdeg2
  obtain ⟨z1, hz1, z2, hz2, hz12⟩ := hdeg2
  rw [mem_neighborFinset] at hz1 hz2
  obtain ⟨z, hz, hzfar⟩ : ∃ z, A.Adj w z ∧ ¬ A.dist u z < A.dist u w := by
    by_contra hcon
    push Not at hcon
    exact hz12 (closer_unique hA hz1 hz2 (hcon z1 hz1) (hcon z2 hz2))
  have hzd : A.dist u w + 1 = A.dist u z := by
    rcases adj_dist hA (u := u) hz with h | h
    · exact h
    · omega
  have hzS : A.dist u z = A.dist u v + A.dist v z := by
    have t1 := hconn.dist_triangle (u := u) (v := v) (w := z)
    have t2 := hconn.dist_triangle (u := v) (v := w) (w := z)
    rw [dist_eq_one_iff_adj.2 hz] at t2
    omega
  have := hwmax z hzS
  omega

end Tree

section Real

variable {X : Type*} {μ : X → X → ℕ}

theorem leaves_in_range {N : ℕ} {A : SimpleGraph (Fin N)} {g : X → Fin N}
    (hmin : IsMinimalRealization μ A g) [DecidableRel A.Adj] (ℓ : Fin N) (h : A.degree ℓ = 1) :
    ℓ ∈ Set.range g := by
  by_contra hℓ
  have hc : ((⊤ : A.Subgraph).induce ({ℓ}ᶜ : Set (Fin N))).Connected :=
    SimpleGraph.connected_induce_iff.1 (hmin.1.1.connected.induce_compl_singleton_of_degree_eq_one h)
  have := hmin.2 _ hc (fun x => by
    simp only [Subgraph.induce_verts, Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hx; exact hℓ ⟨x, hx⟩)
  simp only [Subgraph.induce_verts] at this
  have h2 : ℓ ∈ ({ℓ}ᶜ : Set (Fin N)) := by rw [this]; trivial
  exact h2 rfl

theorem profile_inj {N : ℕ} {A : SimpleGraph (Fin N)} {g : X → Fin N}
    (hmin : IsMinimalRealization μ A g) {u v : Fin N}
    (h : ∀ x, A.dist (g x) u = A.dist (g x) v) : u = v := by
  classical
  by_contra huv
  have hA := hmin.1.1
  obtain ⟨w, ⟨x, rfl⟩, hw⟩ := extend_to_leaf hA (Set.range g) (leaves_in_range hmin) huv
  have hpos := hA.connected.pos_dist_of_ne huv
  have := h x
  rw [SimpleGraph.dist_comm (u := g x), SimpleGraph.dist_comm (u := g x) (v := v)] at this
  omega

theorem adj_of_profile {N : ℕ} {A : SimpleGraph (Fin N)} {g : X → Fin N}
    (hmin : IsMinimalRealization μ A g) {u v : Fin N} (huv : u ≠ v)
    (h : ∀ x, A.dist (g x) u ≤ A.dist (g x) v + 1) : A.Adj u v := by
  classical
  have hA := hmin.1.1
  obtain ⟨w, ⟨x, rfl⟩, hw⟩ := extend_to_leaf hA (Set.range g) (leaves_in_range hmin) huv
  have hpos := hA.connected.pos_dist_of_ne huv
  have := h x
  rw [SimpleGraph.dist_comm (u := g x), SimpleGraph.dist_comm (u := g x) (v := v)] at this
  rw [← dist_eq_one_iff_adj]
  omega

theorem transfer {N N' : ℕ} {A : SimpleGraph (Fin N)} {g : X → Fin N}
    {A' : SimpleGraph (Fin N')} {g' : X → Fin N'}
    (hmin : IsMinimalRealization μ A g) (hmin' : IsMinimalRealization μ A' g') (y0 : X) :
    ∀ n (v : Fin N), A.dist (g y0) v = n → ∃ v' : Fin N', ∀ x, A'.dist (g' x) v' = A.dist (g x) v := by
  classical
  have hA := hmin.1.1
  have hA' := hmin'.1.1
  have hd := hmin.1.2
  have hd' := hmin'.1.2
  intro n
  induction n with
  | zero =>
    intro v hv
    have : g y0 = v := (hA.connected.dist_eq_zero_iff).1 hv
    subst this
    exact ⟨g' y0, fun x => by rw [hd x y0, hd' x y0]⟩
  | succ n ih =>
    intro v hv
    have hvy : v ≠ g y0 := by intro h; subst h; simp at hv
    obtain ⟨u, hvu, hud⟩ := exists_closer hA hvy
    obtain ⟨u', hu'⟩ := ih u (by omega)
    have huv : A.Adj u v := hvu.symm
    obtain ⟨w, ⟨x1, rfl⟩, hw⟩ :=
      extend_to_leaf hA (Set.range g) (leaves_in_range hmin) huv.ne
    rw [dist_eq_one_iff_adj.2 huv] at hw
    have hx1 : A.dist (g x1) u = A.dist (g x1) v + 1 := by
      rw [SimpleGraph.dist_comm (u := g x1), SimpleGraph.dist_comm (u := g x1) (v := v)]; omega
    have hu'x1 : u' ≠ g' x1 := by
      intro h; have := hu' x1; rw [h, SimpleGraph.dist_self] at this; omega
    obtain ⟨w', hw'adj, hw'd⟩ := exists_closer hA' hu'x1
    refine ⟨w', fun x => ?_⟩
    have hAx := adj_dist hA (u := g x) huv
    have hA'x := adj_dist hA' (u := g' x) hw'adj
    rw [hu' x] at hA'x
    have hw'x1 : A'.dist (g' x1) w' + 1 = A.dist (g x1) u := by rw [hw'd, hu' x1]
    rcases hAx with h | h
    · -- `v` is farther from `x` than `u`
      have hμ : μ x1 x = A.dist (g x1) u + A.dist (g x) u := by
        rw [← hd x1 x]
        by_cases hux : u = g x
        · rw [hux, SimpleGraph.dist_self]; rfl
        · obtain ⟨z, hz, hzd⟩ := exists_closer hA hux
          have hzv : v ≠ z := by intro e; subst e; omega
          exact geodesic_of_branches hA huv hz hzv (by omega) (by omega)
      have t := hA'.connected.dist_triangle (u := g' x1) (v := w') (w := g' x)
      rw [hd' x1 x, SimpleGraph.dist_comm (u := w')] at t
      omega
    · -- `v` is closer to `x` than `u`
      by_contra hne
      have h2 : A.dist (g x) u + 1 = A'.dist (g' x) w' := by omega
      have t := hA.connected.dist_triangle (u := g x1) (v := v) (w := g x)
      rw [hd x1 x, SimpleGraph.dist_comm (u := v)] at t
      have hu'x : u' ≠ g' x := by
        intro e; have := hu' x; rw [e, SimpleGraph.dist_self] at this; omega
      obtain ⟨z', hz', hz'd⟩ := exists_closer hA' hu'x
      have hzw : w' ≠ z' := by intro e; subst e; rw [hu' x] at hz'd; omega
      have := geodesic_of_branches hA' hw'adj hz' hzw (by rw [hu' x1]; omega)
        (by rw [hu' x]; rw [hu' x] at hz'd; omega)
      rw [hd' x1 x, hu' x1, hu' x] at this
      omega

theorem exists_match {N N' : ℕ} {A : SimpleGraph (Fin N)} {g : X → Fin N}
    {A' : SimpleGraph (Fin N')} {g' : X → Fin N'}
    (hmin : IsMinimalRealization μ A g) (hmin' : IsMinimalRealization μ A' g') (v : Fin N) :
    ∃ v' : Fin N', ∀ x, A'.dist (g' x) v' = A.dist (g x) v := by
  by_cases hX : Nonempty X
  · obtain ⟨y0⟩ := hX
    exact transfer hmin hmin' y0 _ v rfl
  · obtain ⟨v'⟩ := hmin'.1.1.connected.nonempty
    exact ⟨v', fun x => absurd ⟨x⟩ hX⟩

theorem unique {N N' : ℕ} {A : SimpleGraph (Fin N)} {g : X → Fin N}
    {A' : SimpleGraph (Fin N')} {g' : X → Fin N'}
    (hmin : IsMinimalRealization μ A g) (hmin' : IsMinimalRealization μ A' g') :
    ∃ ψ : A ≃g A', ∀ x : X, ψ (g x) = g' x := by
  choose ψ hψ using exists_match hmin hmin'
  choose ψ' hψ' using exists_match hmin' hmin
  have h1 : ∀ v, ψ' (ψ v) = v := fun v =>
    profile_inj hmin (fun x => by rw [hψ', hψ])
  have h2 : ∀ v', ψ (ψ' v') = v' := fun v' =>
    profile_inj hmin' (fun x => by rw [hψ, hψ'])
  have hconn := hmin.1.1.connected
  have hconn' := hmin'.1.1.connected
  refine ⟨{ toFun := ψ, invFun := ψ', left_inv := h1, right_inv := h2,
            map_rel_iff' := ?_ }, fun x => ?_⟩
  · intro u v
    simp only [Equiv.coe_fn_mk]
    constructor
    · intro h
      have huv : u ≠ v := by intro e; subst e; exact h.ne rfl
      apply adj_of_profile hmin huv
      intro x
      rw [← hψ u x, ← hψ v x]
      have := hconn'.dist_triangle (u := g' x) (v := ψ v) (w := ψ u)
      rw [dist_eq_one_iff_adj.2 h.symm] at this
      exact this
    · intro h
      have huv : ψ u ≠ ψ v := by
        intro e; have := congrArg ψ' e; rw [h1, h1] at this; subst this; exact h.ne rfl
      apply adj_of_profile hmin' huv
      intro x
      rw [hψ u x, hψ v x]
      have := hconn.dist_triangle (u := g x) (v := v) (w := u)
      rw [dist_eq_one_iff_adj.2 h.symm] at this
      exact this
  · simp only [RelIso.coe_fn_mk, Equiv.coe_fn_mk]
    apply profile_inj hmin'
    intro y
    rw [hψ, hmin.1.2, hmin'.1.2]

end Real

theorem leaf_min {N : ℕ} (A : SimpleGraph (Fin N)) [DecidableRel A.Adj] (hA : A.IsTree)
    (S : Set (Fin N)) (hS : ∀ a, A.degree a = 1 → a ∈ S)
    (A' : A.Subgraph) (hc : A'.Connected) (hsub : S ⊆ A'.verts) : A'.verts = Set.univ := by
  classical
  by_contra hne
  obtain ⟨r, hr⟩ := hc.nonempty
  have hW : (Finset.univ.filter (fun v => v ∉ A'.verts)).Nonempty := by
    obtain ⟨v, hv⟩ := (Set.ne_univ_iff_exists_notMem _).1 hne
    exact ⟨v, by simp [hv]⟩
  obtain ⟨v, hvW, hvmax⟩ := Finset.exists_max_image _ (fun v => A.dist r v) hW
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hvW hvmax
  have hrv : r ≠ v := fun h => hvW (h ▸ hr)
  obtain ⟨p, hp, hplen⟩ := hA.connected.exists_path_of_dist r v
  have hpnil : ¬ p.reverse.Nil := by
    rw [← Walk.length_eq_zero_iff]; simp only [Walk.length_reverse]
    intro h0
    exact hrv (Walk.eq_of_length_eq_zero h0)
  set w := p.reverse.snd with hw
  have hvw : A.Adj v w := Walk.adj_snd hpnil
  have hdeg : A.degree v ≠ 1 := fun h1 => hvW (hsub (hS v h1))
  have hdeg0 : 0 < A.degree v := by
    rw [← card_neighborFinset_eq_degree]
    exact Finset.card_pos.2 ⟨w, by simpa using hvw⟩
  obtain ⟨u, hu, huw⟩ : ∃ u ∈ A.neighborFinset v, u ≠ w := by
    by_contra hcon
    push Not at hcon
    have : A.neighborFinset v ⊆ {w} := fun x hx => by simpa using hcon x hx
    have := Finset.card_le_card this
    rw [card_neighborFinset_eq_degree] at this
    simp at this; omega
  rw [mem_neighborFinset] at hu
  obtain ⟨q, hq, hvq⟩ : ∃ q : A.Walk r u, q.IsPath ∧ v ∉ q.support := by
    by_cases huA : u ∈ A'.verts
    · obtain ⟨q0⟩ := hc.preconnected ⟨r, hr⟩ ⟨u, huA⟩
      let q1 : A.Walk r u := q0.map A'.hom
      have hsupp : ∀ x ∈ q1.support, x ∈ A'.verts := by
        intro x hx
        have hx' : x ∈ (q0.map A'.hom).support := hx
        rw [Walk.support_map, List.mem_map] at hx'
        obtain ⟨y, _, rfl⟩ := hx'
        exact y.2
      refine ⟨q1.bypass, q1.bypass_isPath, fun hv => hvW ?_⟩
      exact hsupp v (q1.support_bypass_subset_support hv)
    · have hle : A.dist r u ≤ A.dist r v := hvmax u huA
      obtain ⟨q, hq, hqlen⟩ := hA.connected.exists_path_of_dist r u
      refine ⟨q, hq, fun hv => ?_⟩
      have h1 := q.length_takeUntil_lt_length hv hu.ne
      have h2 := dist_le (q.takeUntil v hv)
      omega
  have hp1 : (Walk.cons hu q.reverse).IsPath :=
    hq.reverse.cons (by simpa using hvq)
  have heq := (hA.isAcyclic.subsingleton_path _ _).elim ⟨_, hp1⟩ ⟨p.reverse, hp.reverse⟩
  have : (Walk.cons hu q.reverse).snd = p.reverse.snd := by
    rw [Subtype.mk.injEq] at heq; rw [heq]
  rw [Walk.snd_cons] at this
  exact huw (this.trans hw.symm)

theorem hom_dist_le {α β : Type*} {A : SimpleGraph α} {B : SimpleGraph β} (f : A →g B)
    {a b : α} (h : A.Reachable a b) : B.dist (f a) (f b) ≤ A.dist a b := by
  obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist
  calc B.dist (f a) (f b) ≤ (p.map f).length := dist_le _
    _ = A.dist a b := by rw [Walk.length_map, hp]

theorem iso_dist {α β : Type*} {A : SimpleGraph α} {B : SimpleGraph β} (ψ : A ≃g B)
    (hA : A.Connected) (a b : α) : B.dist (ψ a) (ψ b) = A.dist a b := by
  apply le_antisymm (hom_dist_le ψ.toHom (hA a b))
  have hr : B.Reachable (ψ a) (ψ b) := (hA a b).map ψ.toHom
  have := hom_dist_le ψ.symm.toHom hr
  simpa using this

theorem induce_dist_tree {α : Type*} [DecidableEq α] {A : SimpleGraph α} (hA : A.IsTree)
    {s : Set α} (hB : (A.induce s).Connected) (a b : s) :
    (A.induce s).dist a b = A.dist a b := by
  obtain ⟨p, hp, hpl⟩ := hB.exists_path_of_dist a b
  have hp' : (p.map (Embedding.induce s).toHom).IsPath :=
    hp.map (Embedding.induce (G := A) s).injective
  have := path_length_eq_dist hA _ hp'
  rw [Walk.length_map, hpl] at this
  exact this

theorem exists_min {X : Type*} {μ : X → X → ℕ} (hμ : IsTreeMetric μ) :
    ∃ (N : ℕ) (A : SimpleGraph (Fin N)) (g : X → Fin N), IsMinimalRealization μ A g := by
  classical
  have hex : ∃ N, ∃ (A : SimpleGraph (Fin N)) (g : X → Fin N), IsRealization μ A g := hμ.2
  obtain ⟨A, g, hreal⟩ := Nat.find_spec hex
  refine ⟨_, A, g, hreal, fun A' hc hsub =>
    leaf_min A hreal.1 (Set.range g) ?_ A' hc (by rintro _ ⟨x, rfl⟩; exact hsub x)⟩
  intro ℓ hℓ
  by_contra hℓg
  let s : Set (Fin (Nat.find hex)) := {ℓ}ᶜ
  have hBc : (A.induce s).Connected :=
    hreal.1.connected.induce_compl_singleton_of_degree_eq_one hℓ
  have hBt : (A.induce s).IsTree :=
    ⟨hBc, hreal.1.isAcyclic.embedding (Embedding.induce s)⟩
  have hM : Fintype.card s < Nat.find hex := by
    have := Fintype.card_subtype_lt (p := fun x => x ∈ s) (x := ℓ) (by simp [s])
    simpa using this
  let ψ := (A.induce s).overFinIso (rfl : Fintype.card s = Fintype.card s)
  have hgs : ∀ x, g x ∈ s := fun x h => hℓg ⟨x, h⟩
  have : ∃ (A : SimpleGraph (Fin (Fintype.card s))) (g : X → Fin (Fintype.card s)),
      IsRealization μ A g :=
    ⟨_, fun x => ψ ⟨g x, hgs x⟩, (Iso.isTree_iff ψ).1 hBt, fun x y => by
      rw [iso_dist ψ hBc, induce_dist_tree hreal.1 hBc]
      exact hreal.2 x y⟩
  exact Nat.find_min hex hM this

end CJUniqueAux

open CJUniqueAux in
theorem solution {X : Type*} (μ : X → X → ℕ) (hμ : IsTreeMetric μ) :
    (∃ (N : ℕ) (A : SimpleGraph (Fin N)) (g : X → Fin N), IsMinimalRealization μ A g) ∧
    ∀ (N : ℕ) (A : SimpleGraph (Fin N)) (g : X → Fin N)
      (N' : ℕ) (A' : SimpleGraph (Fin N')) (g' : X → Fin N'),
      IsMinimalRealization μ A g → IsMinimalRealization μ A' g' →
        ∃ ψ : A ≃g A', ∀ x : X, ψ (g x) = g' x :=
  ⟨exists_min hμ, fun _ _ _ _ _ _ h h' => unique h h'⟩

