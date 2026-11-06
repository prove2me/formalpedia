-- Prove2me | solution 1 for MetricGenerators.ConnectedJoin.three_point
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T20:32:35.51389+00:00
-- url     : https://prove2.me/submissions/dca440a3-f058-4e7a-a201-193b008576c8

import Mathlib
import Definitions.Def_MetricGenerators_ConnectedJoin_TreeMetric

open SimpleGraph MetricGenerators.ConnectedJoin

namespace CJThreePointAux

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

end Tree

/-- In a tree, if `w` is a point of the `p`–`q` geodesic closest to `r`, then `w` lies on the
`r`–`p` geodesic. -/
theorem proj_geodesic {α : Type*} [DecidableEq α] {A : SimpleGraph α} (hA : A.IsTree)
    {p q r w : α} (hw : A.dist p w + A.dist w q = A.dist p q)
    (hmin : ∀ w', A.dist p w' + A.dist w' q = A.dist p q → A.dist r w ≤ A.dist r w') :
    A.dist r p = A.dist r w + A.dist w p := by
  by_cases hwp : w = p
  · subst hwp; simp
  by_cases hwr : w = r
  · subst hwr; simp
  obtain ⟨a, ha, had⟩ := exists_closer hA hwp
  obtain ⟨b, hb, hbd⟩ := exists_closer hA hwr
  have hab : a ≠ b := by
    intro e; subst e
    have t := hA.connected.dist_triangle (u := a) (v := w) (w := q)
    rw [dist_eq_one_iff_adj.2 ha.symm] at t
    have t2 := hA.connected.dist_triangle (u := p) (v := a) (w := q)
    have := hmin a (by omega)
    omega
  have := geodesic_of_branches hA (p := p) (q := r) ha hb hab (by omega) (by omega)
  rw [SimpleGraph.dist_comm (u := r) (v := p), this, SimpleGraph.dist_comm (u := w) (v := p)]
  omega

end CJThreePointAux

open CJThreePointAux in
theorem solution {X : Type*} (μ : X → X → ℕ) {N : ℕ} (A : SimpleGraph (Fin N))
    (g : X → Fin N) (hA : IsRealization μ A g) (x y z : X) (w : Fin N)
    (hw : A.dist (g y) w + A.dist w (g z) = A.dist (g y) (g z))
    (hmin : ∀ w' : Fin N, A.dist (g y) w' + A.dist w' (g z) = A.dist (g y) (g z) →
      A.dist (g x) w ≤ A.dist (g x) w') :
    2 * A.dist (g x) w + μ y z = μ x y + μ x z := by
  have h1 := proj_geodesic hA.1 hw hmin
  have hw' : A.dist (g z) w + A.dist w (g y) = A.dist (g z) (g y) := by
    have e1 := SimpleGraph.dist_comm (G := A) (u := g z) (v := w)
    have e2 := SimpleGraph.dist_comm (G := A) (u := w) (v := g y)
    have e3 := SimpleGraph.dist_comm (G := A) (u := g z) (v := g y)
    omega
  have hmin' : ∀ w', A.dist (g z) w' + A.dist w' (g y) = A.dist (g z) (g y) →
      A.dist (g x) w ≤ A.dist (g x) w' := by
    intro w' h
    apply hmin
    have e1 := SimpleGraph.dist_comm (G := A) (u := g z) (v := w')
    have e2 := SimpleGraph.dist_comm (G := A) (u := w') (v := g y)
    have e3 := SimpleGraph.dist_comm (G := A) (u := g z) (v := g y)
    omega
  have h2 := proj_geodesic hA.1 hw' hmin'
  rw [← hA.2 x y, ← hA.2 x z, ← hA.2 y z, h1, h2, ← hw,
    SimpleGraph.dist_comm (u := w) (v := g y)]
  ring
