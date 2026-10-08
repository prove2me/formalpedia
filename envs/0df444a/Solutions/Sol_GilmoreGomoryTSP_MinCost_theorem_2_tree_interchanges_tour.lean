-- Prove2me | solution 1 for GilmoreGomoryTSP.MinCost.theorem_2_tree_interchanges_tour
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:37:40.62299+00:00
-- url     : https://prove2.me/submissions/6d417576-ff9d-4e3d-9b5e-63750230811b

import Mathlib
import Definitions.Def_GilmoreGomoryTSP_MinCost_Model
import Definitions.Def_GilmoreGomoryTSP_MinCost_Underestimate



namespace GilmoreGomoryTSP.MinCost

variable {n : ℕ}

lemma l1_pow_eq (ψ : Equiv.Perm (Fin (n+1))) (i j : Fin (n+1)) :
    ∀ (m : ℕ) (x : Fin (n+1)), (∀ s < m, (ψ^s) x ≠ i ∧ (ψ^s) x ≠ j) →
      ((ψ * alpha i j)^m) x = (ψ^m) x := by
  intro m
  induction m with
  | zero => intros; simp
  | succ m ih =>
    intro x h
    have h0 := h 0 (Nat.succ_pos m)
    simp only [pow_zero, Equiv.Perm.one_apply] at h0
    have hs : (ψ * alpha i j) x = ψ x := by
      simp only [alpha, Equiv.Perm.mul_apply]
      rw [Equiv.swap_apply_of_ne_of_ne h0.1 h0.2]
    have e1 : ((ψ * alpha i j)^(m+1)) x = ((ψ * alpha i j)^m) ((ψ * alpha i j) x) := by
      rw [pow_succ]; rfl
    have e2 : (ψ^(m+1)) x = (ψ^m) (ψ x) := by rw [pow_succ]; rfl
    rw [e1, e2, hs]
    apply ih
    intro s hsm
    have e : (ψ^s) (ψ x) = (ψ^(s+1)) x := by rw [pow_succ]; rfl
    rw [e]
    exact h (s+1) (by omega)

lemma l1_reach (ψ : Equiv.Perm (Fin (n+1))) (i j : Fin (n+1)) (hij : ¬ ψ.SameCycle i j)
    (x : Fin (n+1)) (hx : ψ.SameCycle i x) : (ψ * alpha i j).SameCycle x i := by
  classical
  by_cases hxi : x = i
  · subst hxi; exact Equiv.Perm.SameCycle.refl _ _
  have hex : ∃ m : ℕ, (ψ^m) x = i := hx.symm.exists_nat_pow_eq
  let m := Nat.find hex
  have hm : (ψ^m) x = i := Nat.find_spec hex
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exfalso; apply hxi; have := hm; rw [h0] at this; simpa using this
    · exact h0
  have hcond : ∀ s < m, (ψ^s) x ≠ i ∧ (ψ^s) x ≠ j := by
    intro s hs
    refine ⟨Nat.find_min hex hs, ?_⟩
    intro hsj
    apply hij
    have h1 : ψ.SameCycle x j := ⟨(s : ℤ), by simpa [zpow_natCast] using hsj⟩
    exact hx.trans h1
  have := l1_pow_eq ψ i j m x hcond
  refine ⟨(m : ℤ), ?_⟩
  rw [zpow_natCast, this, hm]

lemma l1_main {n : ℕ} (ψ : Equiv.Perm (Fin (n + 1))) (i j : Fin (n + 1))
    (hij : ¬ ψ.SameCycle i j) (k l : Fin (n + 1)) :
    (ψ * alpha i j).SameCycle k l ↔
      ψ.SameCycle k l ∨ (ψ.SameCycle k i ∧ ψ.SameCycle l j) ∨
        (ψ.SameCycle k j ∧ ψ.SameCycle l i) := by
  classical
  set σ := ψ * alpha i j with hσ
  let U : Fin (n+1) → Prop := fun x => ψ.SameCycle i x ∨ ψ.SameCycle j x
  have hUcl : ∀ a b, ψ.SameCycle a b → U b → U a := by
    intro a b hab hb
    rcases hb with h | h
    · exact Or.inl (h.trans hab.symm)
    · exact Or.inr (h.trans hab.symm)
  have hUcl' : ∀ a b, ψ.SameCycle a b → U a → U b := by
    intro a b hab ha
    exact hUcl b a hab.symm ha
  have hji : ¬ ψ.SameCycle j i := fun h => hij h.symm
  have hσ' : σ = ψ * alpha j i := by
    simp only [hσ, alpha, Equiv.swap_comm]
  -- reach i
  have hreach_i : ∀ x, ψ.SameCycle i x → σ.SameCycle x i := fun x hx => l1_reach ψ i j hij x hx
  have hreach_j : ∀ x, ψ.SameCycle j x → σ.SameCycle x j := by
    intro x hx
    rw [hσ']
    exact l1_reach ψ j i hji x hx
  have hσi : σ i = ψ j := by
    simp [hσ, alpha]
  have hσj : σ j = ψ i := by
    simp [hσ, alpha]
  have hji_σ : σ.SameCycle j i := by
    have h1 : σ.SameCycle i (ψ j) := ⟨1, by simp [hσi]⟩
    have h2 : σ.SameCycle (ψ j) j := hreach_j _ (Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.SameCycle.refl _ _))
    exact (h1.trans h2).symm
  have hreachU : ∀ x, U x → σ.SameCycle x i := by
    intro x hx
    rcases hx with h | h
    · exact hreach_i x h
    · exact (hreach_j x h).trans hji_σ
  have hstep : ∀ x, ψ.SameCycle x (σ x) ∨ (U x ∧ U (σ x)) := by
    intro x
    by_cases hxi : x = i
    · subst hxi
      right
      refine ⟨Or.inl (Equiv.Perm.SameCycle.refl _ _), ?_⟩
      rw [hσi]
      exact Or.inr (Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.SameCycle.refl _ _))
    by_cases hxj : x = j
    · subst hxj
      right
      refine ⟨Or.inr (Equiv.Perm.SameCycle.refl _ _), ?_⟩
      rw [hσj]
      exact Or.inl (Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.SameCycle.refl _ _))
    · left
      have : σ x = ψ x := by
        simp only [hσ, alpha, Equiv.Perm.mul_apply]
        rw [Equiv.swap_apply_of_ne_of_ne hxi hxj]
      rw [this]
      exact Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.SameCycle.refl _ _)
  have key : σ.SameCycle k l ↔ ψ.SameCycle k l ∨ (U k ∧ U l) := by
    constructor
    · intro h
      obtain ⟨m, hm⟩ := h.exists_nat_pow_eq
      have : ∀ m : ℕ, ψ.SameCycle k ((σ^m) k) ∨ (U k ∧ U ((σ^m) k)) := by
        intro m
        induction m with
        | zero => left; simpa using Equiv.Perm.SameCycle.refl ψ k
        | succ m ih =>
          rw [pow_succ', Equiv.Perm.mul_apply]
          set y := (σ^m) k
          rcases hstep y with h1 | h1
          · rcases ih with h2 | h2
            · left; exact h2.trans h1
            · right; exact ⟨h2.1, hUcl' _ _ h1 h2.2⟩
          · rcases ih with h2 | h2
            · right; exact ⟨hUcl _ _ h2 h1.1, h1.2⟩
            · right; exact ⟨h2.1, h1.2⟩
      rw [← hm]
      exact this m
    · intro h
      rcases h with h | h
      · by_cases hk : U k
        · exact (hreachU k hk).trans (hreachU l (hUcl' _ _ h hk)).symm
        · obtain ⟨m, hm⟩ := h.exists_nat_pow_eq
          have hc : ∀ s < m, (ψ^s) k ≠ i ∧ (ψ^s) k ≠ j := by
            intro s _
            constructor
            · intro hs; apply hk; left
              exact ⟨-(s:ℤ), by rw [zpow_neg, zpow_natCast, Equiv.Perm.inv_eq_iff_eq]; exact hs.symm⟩
            · intro hs; apply hk; right
              exact ⟨-(s:ℤ), by rw [zpow_neg, zpow_natCast, Equiv.Perm.inv_eq_iff_eq]; exact hs.symm⟩
          have := l1_pow_eq ψ i j m k hc
          exact ⟨(m : ℤ), by rw [zpow_natCast, hσ, this, hm]⟩
      · exact (hreachU k h.1).trans (hreachU l h.2).symm
  rw [key]
  constructor
  · rintro (h | ⟨hk, hl⟩)
    · exact Or.inl h
    · rcases hk with hk | hk <;> rcases hl with hl | hl
      · exact Or.inl (hk.symm.trans hl)
      · exact Or.inr (Or.inl ⟨hk.symm, hl.symm⟩)
      · exact Or.inr (Or.inr ⟨hk.symm, hl.symm⟩)
      · exact Or.inl (hk.symm.trans hl)
  · rintro (h | ⟨hk, hl⟩ | ⟨hk, hl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨Or.inl hk.symm, Or.inr hl.symm⟩
    · exact Or.inr ⟨Or.inr hk.symm, Or.inl hl.symm⟩


lemma t2_step {V : Type*} {g h : SimpleGraph V} (hs : ∀ a b, g.Adj a b → h.Reachable a b)
    {x y : V} (hr : g.Reachable x y) : h.Reachable x y := by
  obtain ⟨w⟩ := hr
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj w ih => exact (hs _ _ hadj).trans ih

lemma t2_conn {V : Type*} {g h : SimpleGraph V} (hs : ∀ a b, g.Adj a b → h.Reachable a b)
    (hg : g.Connected) : h.Connected := by
  have : Nonempty V := hg.nonempty
  exact ⟨fun u v => t2_step hs (hg.preconnected u v)⟩

lemma t2_sc_to_reach (σ : Equiv.Perm (Fin (n+1))) {a b : Fin (n+1)} (h : σ.SameCycle a b) :
    (graph σ).Reachable a b := by
  obtain ⟨m, hm⟩ := h.exists_nat_pow_eq
  subst hm
  clear h
  induction m with
  | zero => simp only [pow_zero, Equiv.Perm.one_apply]; exact SimpleGraph.Reachable.refl _
  | succ m ih =>
    refine ih.trans ?_
    rw [pow_succ', Equiv.Perm.mul_apply]
    set y := (σ ^ m) a
    by_cases hy : σ y = y
    · rw [hy]
    · exact SimpleGraph.Adj.reachable (by
        simp only [graph, SimpleGraph.fromRel_adj]
        exact ⟨fun h => hy h.symm, by simp⟩)

lemma t2_reach_to_sc (σ : Equiv.Perm (Fin (n+1))) {a b : Fin (n+1)}
    (h : (graph σ).Reachable a b) : σ.SameCycle a b := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact Equiv.Perm.SameCycle.refl _ _
  | tail _ hadj ih =>
    refine ih.trans ?_
    simp only [graph, SimpleGraph.fromRel_adj] at hadj
    rcases hadj.2 with h | h
    · rw [← h]; exact Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.SameCycle.refl _ _)
    · rw [← h]; exact Equiv.Perm.sameCycle_apply_left.mpr (Equiv.Perm.SameCycle.refl _ _)

lemma t2_tour (σ : Equiv.Perm (Fin (n+1))) (h : ∀ x y, σ.SameCycle x y) : IsTour σ := by
  intro s hne hne' hmap
  obtain ⟨x, hx⟩ := hne
  obtain ⟨y, hy⟩ : ∃ y, y ∉ s := by
    by_contra hc
    push Not at hc
    exact hne' (Finset.eq_univ_of_forall hc)
  obtain ⟨m, hm⟩ := (h x y).exists_nat_pow_eq
  have key : ∀ m : ℕ, (σ^m) x ∈ s := by
    intro m
    induction m with
    | zero => simpa using hx
    | succ m ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      have : σ ((σ^m) x) ∈ s.map σ.toEmbedding := Finset.mem_map_of_mem σ.toEmbedding ih
      rwa [hmap] at this
  exact hy (hm ▸ key m)

lemma t2_gadj_graph (ψ : Equiv.Perm (Fin (n+1))) (E : Finset (Fin (n+1) × Fin (n+1))) {a b}
    (h : (graph ψ).Adj a b) : (graphWith ψ E).Adj a b :=
  (SimpleGraph.sup_adj _ _ _ _).mpr (Or.inl h)

lemma t2_gadj_edge (ψ : Equiv.Perm (Fin (n+1))) (E : Finset (Fin (n+1) × Fin (n+1))) {a b}
    (hab : a ≠ b) (h : (a, b) ∈ E) : (graphWith ψ E).Adj a b :=
  (SimpleGraph.sup_adj _ _ _ _).mpr (Or.inr (by simp only [SimpleGraph.fromRel_adj]; exact ⟨hab, Or.inl h⟩))

lemma t2_gsc (ψ : Equiv.Perm (Fin (n+1))) (E : Finset (Fin (n+1) × Fin (n+1))) {a b}
    (h : ψ.SameCycle a b) : (graphWith ψ E).Reachable a b :=
  t2_step (fun _ _ hadj => (t2_gadj_graph ψ E hadj).reachable) (t2_sc_to_reach ψ h)

lemma t2_gadj_cases (ψ : Equiv.Perm (Fin (n+1))) (E : Finset (Fin (n+1) × Fin (n+1))) {a b}
    (h : (graphWith ψ E).Adj a b) :
    (graph ψ).Adj a b ∨ (a ≠ b ∧ ((a, b) ∈ E ∨ (b, a) ∈ E)) := by
  rcases (SimpleGraph.sup_adj _ _ _ _).mp h with h | h
  · exact Or.inl h
  · right; simpa only [SimpleGraph.fromRel_adj] using h

lemma t2_noloop (ψ : Equiv.Perm (Fin (n+1))) (E : Finset (Fin (n+1) × Fin (n+1)))
    (hE : IsSpanningTree ψ E) (e : Fin (n+1) × Fin (n+1)) (he : e ∈ E) :
    ¬ ψ.SameCycle e.1 e.2 := by
  intro hsc
  apply hE.2 (E.erase e) (Finset.erase_ssubset he)
  refine t2_conn ?_ hE.1
  intro a b hab
  rcases t2_gadj_cases ψ E hab with h | ⟨hne, h | h⟩
  · exact (t2_gadj_graph ψ _ h).reachable
  · by_cases hae : (a, b) = e
    · subst hae; exact t2_gsc ψ _ hsc
    · exact (t2_gadj_edge ψ _ hne (Finset.mem_erase.mpr ⟨hae, h⟩)).reachable
  · by_cases hae : (b, a) = e
    · subst hae; exact (t2_gsc ψ _ hsc).symm
    · exact (t2_gadj_edge ψ _ hne.symm (Finset.mem_erase.mpr ⟨hae, h⟩)).reachable.symm

lemma t2_K1 (ψ : Equiv.Perm (Fin (n+1))) (i j : Fin (n+1)) (hij : ¬ ψ.SameCycle i j)
    (E' : Finset (Fin (n+1) × Fin (n+1))) (a b : Fin (n+1))
    (h : (graphWith (ψ * alpha i j) E').Adj a b) :
    (graphWith ψ (insert (i, j) E')).Reachable a b := by
  have hne : i ≠ j := fun h => hij (h ▸ Equiv.Perm.SameCycle.refl _ _)
  have hij' : (graphWith ψ (insert (i, j) E')).Reachable i j :=
    (t2_gadj_edge ψ _ hne (Finset.mem_insert_self _ _)).reachable
  rcases t2_gadj_cases _ E' h with h | ⟨hne', h | h⟩
  · have hsc := t2_reach_to_sc _ h.reachable
    rcases (l1_main ψ i j hij a b).mp hsc with h1 | ⟨h2, h3⟩ | ⟨h2, h3⟩
    · exact t2_gsc ψ _ h1
    · exact ((t2_gsc ψ _ h2).trans hij').trans (t2_gsc ψ _ h3.symm)
    · exact ((t2_gsc ψ _ h2).trans hij'.symm).trans (t2_gsc ψ _ h3.symm)
  · exact (t2_gadj_edge ψ _ hne' (Finset.mem_insert_of_mem h)).reachable
  · exact (t2_gadj_edge ψ _ hne'.symm (Finset.mem_insert_of_mem h)).reachable.symm

lemma t2_K2 (ψ : Equiv.Perm (Fin (n+1))) (i j : Fin (n+1)) (hij : ¬ ψ.SameCycle i j)
    (E' : Finset (Fin (n+1) × Fin (n+1))) (a b : Fin (n+1))
    (h : (graphWith ψ (insert (i, j) E')).Adj a b) :
    (graphWith (ψ * alpha i j) E').Reachable a b := by
  have hij' : (graphWith (ψ * alpha i j) E').Reachable i j := by
    apply t2_gsc
    exact (l1_main ψ i j hij i j).mpr (Or.inr (Or.inl ⟨Equiv.Perm.SameCycle.refl _ _,
      Equiv.Perm.SameCycle.refl _ _⟩))
  rcases t2_gadj_cases _ _ h with h | ⟨hne', h | h⟩
  · apply t2_gsc
    have hsc : ψ.SameCycle a b := t2_reach_to_sc _ h.reachable
    exact (l1_main ψ i j hij a b).mpr (Or.inl hsc)
  · rcases Finset.mem_insert.mp h with h | h
    · have h' := Prod.mk.inj h
      rw [h'.1, h'.2]; exact hij'
    · exact (t2_gadj_edge _ _ hne' h).reachable
  · rcases Finset.mem_insert.mp h with h | h
    · have h' := Prod.mk.inj h
      rw [h'.1, h'.2]; exact hij'.symm
    · exact (t2_gadj_edge _ _ hne'.symm h).reachable.symm

lemma t2_main : ∀ (L : List (Fin (n+1) × Fin (n+1))) (ψ : Equiv.Perm (Fin (n+1))),
    L.Nodup → IsSpanningTree ψ L.toFinset →
      IsTour (L.foldl (fun σ e => σ * alpha e.1 e.2) ψ)
  | [], ψ, _, hT => by
    simp only [List.foldl_nil]
    apply t2_tour
    intro x y
    have hc : (graph ψ).Connected := by
      refine t2_conn ?_ hT.1
      intro a b hab
      rcases t2_gadj_cases ψ _ hab with h | ⟨_, h | h⟩
      · exact h.reachable
      · simp at h
      · simp at h
    exact t2_reach_to_sc ψ (hc.preconnected x y)
  | (i, j) :: L, ψ, hnd, hT => by
    have heL : (i, j) ∉ L := (List.nodup_cons.mp hnd).1
    have hL : L.Nodup := (List.nodup_cons.mp hnd).2
    have hnot : (i, j) ∉ L.toFinset := by simpa using heL
    have hE : ((i, j) :: L).toFinset = insert (i, j) L.toFinset := by simp
    rw [hE] at hT
    have hsc : ¬ψ.SameCycle i j := t2_noloop ψ _ hT (i, j) (Finset.mem_insert_self _ _)
    simp only [List.foldl_cons]
    apply t2_main L _ hL
    refine ⟨t2_conn (t2_K2 ψ i j hsc L.toFinset) hT.1, ?_⟩
    intro E'' hsub hconn
    apply hT.2 (insert (i, j) E'')
    · rw [Finset.ssubset_iff_subset_ne]
      refine ⟨Finset.insert_subset_insert _ hsub.subset, fun heq => ?_⟩
      apply hsub.not_subset
      intro x hx
      have : x ∈ insert (i, j) E'' := heq ▸ Finset.mem_insert_of_mem hx
      rcases Finset.mem_insert.mp this with rfl | h
      · exact absurd hx hnot
      · exact h
    · exact t2_conn (t2_K1 ψ i j hsc E'') hconn

theorem theorem_2_core {n : ℕ} (ψ : Equiv.Perm (Fin (n + 1)))
    (L : List (Fin (n + 1) × Fin (n + 1))) (hL : L.Nodup) (hT : IsSpanningTree ψ L.toFinset) :
    IsTour (L.foldl (fun σ e => σ * alpha e.1 e.2) ψ) := t2_main L ψ hL hT

end GilmoreGomoryTSP.MinCost

open GilmoreGomoryTSP.MinCost


theorem solution {n : ℕ} (ψ : Equiv.Perm (Fin (n + 1)))
    (L : List (Fin (n + 1) × Fin (n + 1))) (hL : L.Nodup) (hT : IsSpanningTree ψ L.toFinset) :
    IsTour (L.foldl (fun σ e => σ * alpha e.1 e.2) ψ) := by
  exact theorem_2_core ψ L hL hT
