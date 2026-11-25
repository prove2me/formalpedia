-- Prove2me | solution 2 for Menger.Aux.fam_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:51:49.836488+00:00
-- url     : https://prove2.me/submissions/448cabed-5945-4f5f-9fe6-00fa916942b7

module
public import Mathlib
public import Definitions.Def_MengerHamilton_MengerCore
public import Theorems.Thm_Menger_Aux_Sep_symm
public import Theorems.Thm_Menger_Aux_R_not_mem
public import Theorems.Thm_Menger_Aux_R_of_mem
public import Theorems.Thm_Menger_Aux_R_disj
public import Theorems.Thm_Menger_Aux_path_R
public import Theorems.Thm_Menger_Aux_sep_transfer
public import Theorems.Thm_Menger_Aux_surj_of_inj

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Menger Menger.Aux
variable {V : Type*}
namespace Menger.Aux
theorem _root_.solution {G : SimpleGraph V} {e : Sym2 V} {x y : V} (hxy : G.Adj x y)
    (he : s(x, y) = e) {A B Y : Finset V} {k : ℕ}
    (hY : Sep (G.deleteEdges {e}) A B Y) (hYk : Y.card < k)
    (hk : ∀ X, Sep G A B X → k ≤ X.card)
    (hRx : R (G.deleteEdges {e}) A Y x) (hRy : R (G.deleteEdges {e}) B Y y)
    (IH : ∀ A' B' : Finset V, (∀ X, Sep (G.deleteEdges {e}) A' B' X → k ≤ X.card) →
      Fam (G.deleteEdges {e}) A' B' k) : Fam G A B k := by
  classical
  have hle : G.deleteEdges {e} ≤ G := G.deleteEdges_le _
  have hdisj : ∀ w, R (G.deleteEdges {e}) A Y w → R (G.deleteEdges {e}) B Y w → False :=
    fun w h1 h2 => R_disj hY h1 h2
  have hxY : x ∉ Y := hRx.not_mem
  have hyY : y ∉ Y := hRy.not_mem
  have hxney : x ≠ y := hxy.ne
  have hsep1 : Sep G A B (insert x Y) := by
    intro a ha b hb q
    by_cases hq : e ∈ q.edges
    · exact ⟨x, Finset.mem_insert_self _ _, q.fst_mem_support_of_mem_edges (by rw [he]; exact hq)⟩
    · obtain ⟨v, hv, hvs⟩ := hY a ha b hb (q.toDeleteEdges {e} (fun e' he' h' => hq (by
        rw [Set.mem_singleton_iff] at h'
        exact h' ▸ he')))
      exact ⟨v, Finset.mem_insert_of_mem hv, by simpa using hvs⟩
  have hc1 : (insert x Y).card = Y.card + 1 := Finset.card_insert_of_notMem hxY
  have hk1 := hk _ hsep1
  have hk0 : 0 < k := by omega
  have hc2 : (insert y Y).card = k := by rw [Finset.card_insert_of_notMem hyY]; omega
  have hc1' : (insert x Y).card = k := by omega
  obtain ⟨P, hP, hPd⟩ := IH A (insert x Y)
    (fun Z hZ => hk Z (sep_transfer he hY (fun h => hdisj y h hRy) hZ))
  obtain ⟨Q, hQ, hQd⟩ := IH B (insert y Y)
    (fun Z hZ => hk Z (sep_transfer (x := y) (y := x) (by rw [Sym2.eq_swap]; exact he) hY.symm
      (fun h => hdisj x hRx h) hZ).symm)
  have FP : ∀ i, ∀ w ∈ (P i).2.2.support, w = (P i).2.1 ∨ R (G.deleteEdges {e}) A Y w := by
    intro i w hw
    by_cases h : w = (P i).2.1
    · exact Or.inl h
    · exact Or.inr (path_R (Finset.subset_insert _ _) (hP i).1 _ (hP i).2.2.1 (hP i).2.2.2.2 hw h)
  have FQ : ∀ j, ∀ w ∈ (Q j).2.2.support, w = (Q j).2.1 ∨ R (G.deleteEdges {e}) B Y w := by
    intro j w hw
    by_cases h : w = (Q j).2.1
    · exact Or.inl h
    · exact Or.inr (path_R (Finset.subset_insert _ _) (hQ j).1 _ (hQ j).2.2.1 (hQ j).2.2.2.2 hw h)
  have hQinj : Function.Injective (fun j => (Q j).2.1) := by
    intro j j' h
    by_contra hne
    exact hQd j j' hne _ (Q j).2.2.end_mem_support
      (by simp only at h; rw [h]; exact (Q j').2.2.end_mem_support)
  have hQsurj := surj_of_inj (fun j => (Q j).2.1) (fun j => (hQ j).2.1) hQinj hc2.le
  have hJex : ∀ v, ∃ j : Fin k, v ∈ insert y Y → (Q j).2.1 = v := by
    intro v
    by_cases hv : v ∈ insert y Y
    · obtain ⟨j, hj⟩ := hQsurj v hv
      exact ⟨j, fun _ => hj⟩
    · exact ⟨⟨0, hk0⟩, fun h => absurd h hv⟩
  choose J hJ using hJex
  let σ : V → V := fun v => if v = x then y else v
  have hσX : ∀ v ∈ insert x Y, σ v ∈ insert y Y := by
    intro v hv
    by_cases h : v = x
    · simp [σ, h]
    · simp only [σ, h, ite_false]
      exact Finset.mem_insert_of_mem ((Finset.mem_insert.1 hv).resolve_left h)
  have hσinj : ∀ v ∈ insert x Y, ∀ v' ∈ insert x Y, σ v = σ v' → v = v' := by
    intro v hv v' hv' h
    by_cases h1 : v = x <;> by_cases h2 : v' = x <;> simp only [σ, h1, h2, ite_true, ite_false] at h
    · rw [h1, h2]
    · exact absurd ((Finset.mem_insert.1 hv').resolve_left h2) (h ▸ hyY)
    · exact absurd ((Finset.mem_insert.1 hv).resolve_left h1) (h ▸ hyY)
    · exact h
  let jj : Fin k → Fin k := fun i => J (σ (P i).2.1)
  have hm : ∀ i, (Q (jj i)).2.1 = σ (P i).2.1 := fun i => hJ _ (hσX _ (hP i).2.1)
  have hlink : ∀ i, ∃ l : G.Walk (P i).2.1 (Q (jj i)).2.1,
      ∀ w ∈ l.support, w = (P i).2.1 ∨ w = (Q (jj i)).2.1 := by
    intro i
    by_cases hv : (P i).2.1 = x
    · have h1 : (Q (jj i)).2.1 = y := by rw [hm]; simp [σ, hv]
      refine ⟨(Walk.cons hxy Walk.nil).copy hv.symm h1.symm, fun w hw => ?_⟩
      simp only [Walk.support_copy, Walk.support_cons, Walk.support_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact Or.inl hv.symm
      · exact Or.inr h1.symm
    · have h1 : (Q (jj i)).2.1 = (P i).2.1 := by rw [hm]; simp [σ, hv]
      refine ⟨Walk.nil.copy rfl h1.symm, fun w hw => ?_⟩
      simp only [Walk.support_copy, Walk.support_nil, List.mem_singleton] at hw
      exact Or.inl hw
  choose L hL using hlink
  let W : Fin k → Σ a b : V, G.Walk a b := fun i =>
    ⟨(P i).1, (Q (jj i)).1, (((P i).2.2.mapLe hle).append
      ((L i).append ((Q (jj i)).2.2.reverse.mapLe hle))).bypass⟩
  have hWsupp : ∀ i, ∀ w ∈ (W i).2.2.support,
      w ∈ (P i).2.2.support ∨ w ∈ (Q (jj i)).2.2.support := by
    intro i w hw
    have hw' := Walk.support_bypass_subset_support _ hw
    simp only [Walk.mem_support_append_iff, Walk.support_mapLe_eq_support, Walk.support_reverse,
      List.mem_reverse] at hw'
    rcases hw' with h | h | h
    · exact Or.inl h
    · rcases hL i w h with rfl | rfl
      · exact Or.inl (P i).2.2.end_mem_support
      · exact Or.inr (Q (jj i)).2.2.end_mem_support
    · exact Or.inr h
  have hvinj : ∀ i i', i ≠ i' → (P i).2.1 ≠ (P i').2.1 := by
    intro i i' h heq
    have h2 : (P i).2.1 ∈ (P i').2.2.support := by rw [heq]; exact (P i').2.2.end_mem_support
    exact hPd i i' h _ (P i).2.2.end_mem_support h2
  have hjinj : ∀ i i', i ≠ i' → jj i ≠ jj i' := by
    intro i i' h heq
    have : σ (P i).2.1 = σ (P i').2.1 := by rw [← hm, ← hm, heq]
    exact hvinj i i' h (hσinj _ (hP i).2.1 _ (hP i').2.1 this)
  have hPQ : ∀ i i', i ≠ i' → ∀ w ∈ (P i).2.2.support, w ∉ (Q (jj i')).2.2.support := by
    intro i i' hii w hw hw'
    have hvX : (P i).2.1 ∈ insert x Y := (hP i).2.1
    rcases FP i w hw with h1 | h1 <;> rcases FQ (jj i') w hw' with h2 | h2
    · rw [hm] at h2
      by_cases hv' : (P i').2.1 = x
      · simp only [σ, hv', ite_true] at h2
        rw [← h1, h2] at hvX
        rcases Finset.mem_insert.1 hvX with h | h
        · exact hxney h.symm
        · exact hyY h
      · simp only [σ, hv', ite_false] at h2
        exact hvinj i i' hii (h1.symm.trans h2)
    · rw [← h1] at hvX
      rcases Finset.mem_insert.1 hvX with h | h
      · exact hdisj x (h ▸ hRx) (h ▸ h2)
      · exact h2.not_mem h
    · have hmX : (Q (jj i')).2.1 ∈ insert y Y := (hQ _).2.1
      rw [← h2] at hmX
      rcases Finset.mem_insert.1 hmX with h | h
      · exact hdisj y (h ▸ h1) hRy
      · exact h1.not_mem h
    · exact hdisj w h1 h2
  refine ⟨W, fun i => ⟨(hP i).1, (hQ (jj i)).1, Walk.bypass_isPath _, ?_, ?_⟩, ?_⟩
  · intro w hw hwA
    rcases hWsupp i w hw with h | h
    · exact (hP i).2.2.2.1 w h hwA
    · rcases FQ (jj i) w h with h' | h'
      · rw [hm] at h'
        by_cases hv : (P i).2.1 = x
        · simp only [σ, hv, ite_true] at h'
          subst h'
          exact (hdisj _ (R.of_mem hwA hyY) hRy).elim
        · simp only [σ, hv, ite_false] at h'
          exact (hP i).2.2.2.1 w (h' ▸ (P i).2.2.end_mem_support) hwA
      · exact (hdisj w (R.of_mem hwA h'.not_mem) h').elim
  · intro w hw hwB
    rcases hWsupp i w hw with h | h
    · rcases FP i w h with h' | h'
      · by_cases hv : (P i).2.1 = x
        · rw [hv] at h'
          subst h'
          exact (hdisj _ hRx (R.of_mem hwB hxY)).elim
        · have : w = (Q (jj i)).2.1 := by rw [hm]; simp [σ, hv, h']
          exact (hQ (jj i)).2.2.2.1 w (this ▸ (Q (jj i)).2.2.end_mem_support) hwB
      · exact (hdisj w h' (R.of_mem hwB h'.not_mem)).elim
    · exact (hQ (jj i)).2.2.2.1 w h hwB
  · intro i i' hii w hw hw'
    rcases hWsupp i w hw with h | h <;> rcases hWsupp i' w hw' with h' | h'
    · exact hPd i i' hii w h h'
    · exact hPQ i i' hii w h h'
    · exact hPQ i' i (Ne.symm hii) w h' h
    · exact hQd _ _ (hjinj i i' hii) w h h'
end Menger.Aux
