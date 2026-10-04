-- Prove2me | solution 1 for HadwigerConj.wagner_colorable_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T03:32:29.596878+00:00
-- url     : https://prove2.me/submissions/c10b2f1a-ba16-486e-ba68-7595b7211589

import Mathlib
import Definitions.Def_HadwigerConj_Defs

open SimpleGraph

namespace WagnerAux

/-- A choice of a root in every connected component. -/
structure Root {V : Type} (G : SimpleGraph V) (r : V → V) : Prop where
  reach : ∀ v, G.Reachable (r v) v
  eq : ∀ u v, G.Reachable u v → r u = r v

lemma exists_root {V : Type} (G : SimpleGraph V) : ∃ r : V → V, Root G r := by
  refine ⟨fun v => (G.connectedComponentMk v).out, ⟨fun v => ?_, fun u v h => ?_⟩⟩
  · have := Quot.out_eq (G.connectedComponentMk v)
    exact (ConnectedComponent.eq.mp this)
  · have : G.connectedComponentMk u = G.connectedComponentMk v := ConnectedComponent.eq.mpr h
    simp [this]

/-- Distance to the root of the component. -/
noncomputable def dd {V : Type} (G : SimpleGraph V) (r : V → V) (v : V) : ℕ := G.dist (r v) v

section

variable {V : Type} {G : SimpleGraph V} {r : V → V}

lemma Root.adj_root (h : Root G r) {u v : V} (hadj : G.Adj u v) : r u = r v :=
  h.eq u v hadj.reachable

lemma Root.dd_le_succ (h : Root G r) {u v : V} (hadj : G.Adj u v) :
    dd G r u ≤ dd G r v + 1 := by
  obtain ⟨p, hp⟩ := (h.reach v).exists_walk_length_eq_dist
  have h1 : G.dist (r v) u ≤ (p.concat hadj.symm).length := dist_le _
  rw [Walk.length_concat] at h1
  unfold dd
  rw [h.adj_root hadj]
  omega

lemma Root.root_root (h : Root G r) (v : V) : r (r v) = r v := h.eq _ _ (h.reach v)

lemma Root.dd_root (h : Root G r) (v : V) : dd G r (r v) = 0 := by
  unfold dd
  rw [h.root_root]
  exact dist_self

lemma Root.eq_root_of_dd_zero (h : Root G r) {v : V} (hv : dd G r v = 0) : v = r v :=
  ((h.reach v).dist_eq_zero_iff.mp hv).symm

lemma Root.exists_pred (h : Root G r) {v : V} {k : ℕ} (hk : dd G r v = k + 1) :
    ∃ w, G.Adj v w ∧ dd G r w ≤ k := by
  obtain ⟨p, hp⟩ := (h.reach v).exists_walk_length_eq_dist
  have hne : v ≠ r v := by
    intro hv
    have h0 : dd G r v = 0 := by
      unfold dd
      rw [← hv]
      exact dist_self
    omega
  obtain ⟨w, hadj, q, hq⟩ := Walk.exists_eq_cons_of_ne hne p.reverse
  refine ⟨w, hadj, ?_⟩
  have hlen : q.length = k := by
    have h1 := congrArg Walk.length hq
    rw [Walk.length_reverse, Walk.length_cons] at h1
    unfold dd at hk
    omega
  have h2 : G.dist (r v) w ≤ q.reverse.length := dist_le _
  rw [Walk.length_reverse] at h2
  unfold dd
  rw [← h.adj_root hadj]
  omega

end

section

variable {V : Type} {G : SimpleGraph V} {r : V → V}

/-- The set of vertices of the component of `ρ` at distance `< δ` from the root. -/
def ball (G : SimpleGraph V) (r : V → V) (ρ : V) (δ : ℕ) : Set V :=
  {u | r u = ρ ∧ dd G r u < δ}

lemma Root.ball_connected (h : Root G r) (v0 : V) (δ : ℕ) (hδ : 1 ≤ δ) :
    (G.induce (ball G r (r v0) δ)).Connected := by
  have hρ : r v0 ∈ ball G r (r v0) δ := ⟨h.root_root v0, by rw [h.dd_root]; omega⟩
  have key : ∀ k : ℕ, ∀ (u : V) (hu : u ∈ ball G r (r v0) δ), dd G r u ≤ k →
      (G.induce (ball G r (r v0) δ)).Reachable ⟨r v0, hρ⟩ ⟨u, hu⟩ := by
    intro k
    induction k with
    | zero =>
      intro u hu hd
      have h1 : u = r u := h.eq_root_of_dd_zero (by omega)
      have h2 : u = r v0 := by rw [h1]; exact hu.1
      subst h2
      exact Reachable.refl _
    | succ k ih =>
      intro u hu hd
      by_cases hle : dd G r u ≤ k
      · exact ih u hu hle
      · have hk : dd G r u = k + 1 := by omega
        obtain ⟨w, hadj, hw⟩ := h.exists_pred hk
        have hwr : r w = r v0 := by rw [← h.adj_root hadj]; exact hu.1
        have hwb : w ∈ ball G r (r v0) δ := ⟨hwr, by have := hu.2; omega⟩
        have hrw := ih w hwb hw
        have hadj' : (G.induce (ball G r (r v0) δ)).Adj ⟨w, hwb⟩ ⟨u, hu⟩ := hadj.symm
        exact hrw.trans hadj'.reachable
  rw [connected_iff]
  refine ⟨fun a b => ?_, ⟨⟨r v0, hρ⟩⟩⟩
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  exact (key _ a ha le_rfl).symm.trans (key _ b hb le_rfl)

end

/-- The graph keeping only the edges inside a layer. -/
def layerGraph {V : Type} (G : SimpleGraph V) (d : V → ℕ) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ d u = d v
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h.1⟩

section

variable {V : Type} {G : SimpleGraph V} {r : V → V}

lemma Root.layer_reach (h : Root G r) {u v : V} (huv : (layerGraph G (dd G r)).Reachable u v) :
    dd G r u = dd G r v ∧ r u = r v := by
  rw [reachable_iff_reflTransGen] at huv
  induction huv with
  | refl => exact ⟨rfl, rfl⟩
  | tail _ hbc ih => exact ⟨ih.1.trans hbc.2, ih.2.trans (h.adj_root hbc.1)⟩

lemma Root.layer_induce_reach (h : Root G r) {s : Set V} {u v : V} (hu : u ∈ s) (hv : v ∈ s)
    (huv : ((layerGraph G (dd G r)).induce s).Reachable ⟨u, hu⟩ ⟨v, hv⟩) :
    dd G r u = dd G r v ∧ r u = r v := by
  apply h.layer_reach
  have := huv.map (Embedding.induce (G := layerGraph G (dd G r)) s).toHom
  simpa using this

end

section

variable {V : Type} {G : SimpleGraph V} {r : V → V}

/-- A `K_{t+1}` minor inside a layer, together with the ball below the layer, gives a
`K_{t+2}` minor of `G`. -/
lemma Root.no_minor_layer (h : Root G r) {t : ℕ} (ht : 1 ≤ t)
    (hG : ¬ HadwigerConj.HasCompleteMinor G (t + 2)) :
    ¬ HadwigerConj.HasCompleteMinor (layerGraph G (dd G r)) (t + 1) := by
  intro hmin
  obtain ⟨B, hconn, hdisj, hadj⟩ := hmin
  have hsame : ∀ (i : Fin (t + 1)) (u v : V), u ∈ B i → v ∈ B i →
      dd G r u = dd G r v ∧ r u = r v := by
    intro i u v hu hv
    exact h.layer_induce_reach hu hv ((hconn i).preconnected ⟨u, hu⟩ ⟨v, hv⟩)
  have hne : ∀ i, ∃ u, u ∈ B i := fun i => by
    obtain ⟨⟨u, hu⟩⟩ := (hconn i).nonempty
    exact ⟨u, hu⟩
  obtain ⟨u0, hu0⟩ := hne 0
  have hlayer : ∀ (i : Fin (t + 1)) (u : V), u ∈ B i →
      dd G r u = dd G r u0 ∧ r u = r u0 := by
    intro i u hu
    by_cases hi : i = 0
    · subst hi
      exact hsame 0 u u0 hu hu0
    · obtain ⟨x, hx, y, hy, hxy⟩ := hadj 0 i ((top_adj _ _).2 (Ne.symm hi))
      have e1 := hsame 0 x u0 hx hu0
      have e2 := hsame i u y hu hy
      exact ⟨e2.1.trans (hxy.2.symm.trans e1.1),
        e2.2.trans ((h.adj_root hxy.1).symm.trans e1.2)⟩
  have hδ : 1 ≤ dd G r u0 := by
    by_contra hlt
    have h0 : dd G r u0 = 0 := by omega
    obtain ⟨u1, hu1⟩ := hne ⟨1, by omega⟩
    have e1 := hlayer ⟨1, by omega⟩ u1 hu1
    have hr0 : u0 = r u0 := h.eq_root_of_dd_zero h0
    have hr1 : u1 = r u1 := h.eq_root_of_dd_zero (e1.1.trans h0)
    have h01 : u0 = u1 := hr0.trans (e1.2.symm.trans hr1.symm)
    have hd := hdisj 0 ⟨1, by omega⟩ (by
      intro heq
      have := congrArg Fin.val heq
      simp at this)
    exact Set.disjoint_left.mp hd hu0 (by rw [h01]; exact hu1)
  have hball_adj : ∀ j : Fin (t + 1), ∃ w ∈ ball G r (r u0) (dd G r u0),
      ∃ v ∈ B j, G.Adj w v := by
    intro j
    obtain ⟨v, hv⟩ := hne j
    have ev := hlayer j v hv
    obtain ⟨k, hk⟩ : ∃ k, dd G r v = k + 1 := ⟨dd G r v - 1, by omega⟩
    obtain ⟨w, hadjw, hw⟩ := h.exists_pred hk
    exact ⟨w, ⟨(h.adj_root hadjw).symm.trans ev.2, by omega⟩, v, hv, hadjw.symm⟩
  apply hG
  refine ⟨Fin.cons (α := fun _ : Fin (t + 2) => Set V)
    (ball G r (r u0) (dd G r u0)) B, ?_, ?_, ?_⟩
  · intro i
    induction i using Fin.cases with
    | zero =>
      exact h.ball_connected u0 (dd G r u0) hδ
    | succ j =>
      refine Connected.mono ?_ (hconn j)
      intro a b hab
      exact hab.1
  · intro w₁ w₂ hne12
    induction w₁ using Fin.cases with
    | zero =>
      induction w₂ using Fin.cases with
      | zero => exact absurd rfl hne12
      | succ j =>
        simp only [Fin.cons_zero, Fin.cons_succ]
        refine Set.disjoint_left.mpr (fun u hu hu' => ?_)
        have h1 := (hlayer j u hu').1
        have h2 := hu.2
        omega
    | succ i =>
      induction w₂ using Fin.cases with
      | zero =>
        simp only [Fin.cons_zero, Fin.cons_succ]
        refine Set.disjoint_left.mpr (fun u hu hu' => ?_)
        have h1 := (hlayer i u hu).1
        have h2 := hu'.2
        omega
      | succ j =>
        simp only [Fin.cons_succ]
        exact hdisj i j (fun heq => hne12 (congrArg Fin.succ heq))
  · intro w₁ w₂ hw
    have hne12 : w₁ ≠ w₂ := (top_adj _ _).1 hw
    induction w₁ using Fin.cases with
    | zero =>
      induction w₂ using Fin.cases with
      | zero => exact absurd rfl hne12
      | succ j =>
        simp only [Fin.cons_zero, Fin.cons_succ]
        exact hball_adj j
    | succ i =>
      induction w₂ using Fin.cases with
      | zero =>
        simp only [Fin.cons_zero, Fin.cons_succ]
        obtain ⟨w, hw', v, hv, hadjv⟩ := hball_adj i
        exact ⟨v, hv, w, hw', hadjv.symm⟩
      | succ j =>
        simp only [Fin.cons_succ]
        obtain ⟨x, hx, y, hy, hxy⟩ :=
          hadj i j ((top_adj _ _).2 (fun heq => hne12 (congrArg Fin.succ heq)))
        exact ⟨x, hx, y, hy, hxy.1⟩

end

section

variable {V : Type} {G : SimpleGraph V} {r : V → V}

/-- Doubling the palette by the parity of the distance to the root. -/
lemma Root.colorable_double (h : Root G r) {n : ℕ}
    (hH : (layerGraph G (dd G r)).Colorable n) : G.Colorable (2 * n) := by
  obtain ⟨c⟩ := hH
  let C : G.Coloring (Fin 2 × Fin n) :=
    Coloring.mk (fun v => (⟨dd G r v % 2, Nat.mod_lt _ (by norm_num)⟩, c v)) (by
      intro u v huv heq
      have hsnd : c u = c v := congrArg Prod.snd heq
      have hfst : dd G r u % 2 = dd G r v % 2 := by
        have := congrArg (fun x => (x.1 : ℕ)) heq
        simpa using this
      by_cases hd : dd G r u = dd G r v
      · exact c.valid (show (layerGraph G (dd G r)).Adj u v from ⟨huv, hd⟩) hsnd
      · have h1 := h.dd_le_succ huv
        have h2 := h.dd_le_succ huv.symm
        omega)
  have := C.colorable
  simpa [Fintype.card_prod] using this

end

lemma singleton_connected {V : Type} (G : SimpleGraph V) (v : V) :
    (G.induce ({v} : Set V)).Connected := by
  rw [connected_iff]
  refine ⟨fun a b => ?_, ⟨⟨v, rfl⟩⟩⟩
  have hab : a = b := Subtype.ext (a.2.trans b.2.symm)
  subst hab
  exact Reachable.refl _

lemma colorable_of_no_k1 {V : Type} (G : SimpleGraph V)
    (hG : ¬ HadwigerConj.HasCompleteMinor G 1) : G.Colorable 1 := by
  have hV : IsEmpty V := by
    refine ⟨fun v => hG ?_⟩
    refine ⟨fun _ => {v}, fun _ => singleton_connected G v, fun w₁ w₂ hne => ?_,
      fun w₁ w₂ hw => ?_⟩
    · exact absurd (Subsingleton.elim w₁ w₂) hne
    · exact absurd (Subsingleton.elim w₁ w₂) ((top_adj _ _).1 hw)
  exact ⟨Coloring.mk (fun v => isEmptyElim v) (fun {v} => isEmptyElim v)⟩

lemma colorable_of_no_k2 {V : Type} (G : SimpleGraph V)
    (hG : ¬ HadwigerConj.HasCompleteMinor G 2) : G.Colorable 2 := by
  have hno : ∀ u v, ¬ G.Adj u v := by
    intro u v huv
    apply hG
    refine ⟨![({u} : Set V), {v}], fun i => ?_, fun w₁ w₂ hne => ?_, fun w₁ w₂ hw => ?_⟩
    · fin_cases i
      · exact singleton_connected G u
      · exact singleton_connected G v
    · fin_cases w₁ <;> fin_cases w₂
      · exact absurd rfl hne
      · simpa using huv.ne
      · simpa using huv.ne.symm
      · exact absurd rfl hne
    · fin_cases w₁ <;> fin_cases w₂
      · exact absurd rfl ((top_adj _ _).1 hw)
      · exact ⟨u, rfl, v, rfl, huv⟩
      · exact ⟨v, rfl, u, rfl, huv.symm⟩
      · exact absurd rfl ((top_adj _ _).1 hw)
  exact ⟨Coloring.mk (fun _ => 0) (fun {u v} huv => absurd huv (hno u v))⟩

/-- Wagner's theorem. -/
theorem wagner_aux {V : Type} : ∀ (t : ℕ) (G : SimpleGraph V),
    ¬ HadwigerConj.HasCompleteMinor G (t + 1) → G.Colorable (2 ^ t)
  | 0, G, hG => by simpa using colorable_of_no_k1 G hG
  | 1, G, hG => by simpa using colorable_of_no_k2 G hG
  | t + 2, G, hG => by
    obtain ⟨r, hr⟩ := exists_root G
    have hH : (layerGraph G (dd G r)).Colorable (2 ^ (t + 1)) :=
      wagner_aux (t + 1) _ (hr.no_minor_layer (by omega) hG)
    have := hr.colorable_double hH
    simpa [pow_succ, mul_comm] using this

end WagnerAux

theorem solution (t : ℕ) {V : Type} [Finite V] (G : SimpleGraph V)
    (hG : ¬ HadwigerConj.HasCompleteMinor G (t + 1)) : G.Colorable (2 ^ t) :=
  WagnerAux.wagner_aux t G hG
