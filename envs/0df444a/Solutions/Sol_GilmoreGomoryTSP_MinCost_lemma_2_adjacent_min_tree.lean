-- Prove2me | solution 1 for GilmoreGomoryTSP.MinCost.lemma_2_adjacent_min_tree
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:58:03.166722+00:00
-- url     : https://prove2.me/submissions/fcf1154d-a41b-4489-b804-3b2ece4ab184

import Mathlib
import Definitions.Def_GilmoreGomoryTSP_MinCost_Model
import Definitions.Def_GilmoreGomoryTSP_MinCost_Underestimate



namespace GilmoreGomoryTSP.MinCost

open MeasureTheory

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

lemma e11_ii (f : ℝ → ℝ) (hf : LocallyIntegrable f) (a b : ℝ) :
    IntervalIntegrable f volume a b :=
  (hf.integrableOn_isCompact isCompact_uIcc).intervalIntegrable

noncomputable def e11F (φ γ : ℝ → ℝ) (u v : ℝ) : ℝ := if u ≤ v then φ v - φ u else γ u - γ v

lemma e11_c (f g : ℝ → ℝ) (hf : LocallyIntegrable f) (hg : LocallyIntegrable g)
    (A B : Fin (n + 1) → ℝ) (i j : Fin (n + 1)) :
    c f g A B i j = e11F (fun t => ∫ x in (0:ℝ)..t, f x) (fun t => ∫ x in (0:ℝ)..t, g x)
      (B i) (A j) := by
  unfold c e11F
  split_ifs with h
  · rw [← intervalIntegral.integral_interval_sub_left (e11_ii f hf _ _) (e11_ii f hf _ _)]
  · rw [← intervalIntegral.integral_interval_sub_left (e11_ii g hg _ _) (e11_ii g hg _ _)]

lemma e11_alg (φ γ : ℝ → ℝ) (a b p q : ℝ) (hab : a ≤ b) (hpq : p ≤ q) :
    e11F φ γ a q + e11F φ γ b p - e11F φ γ a p - e11F φ γ b q =
      if max a p ≤ min b q then (φ (min b q) + γ (min b q)) - (φ (max a p) + γ (max a p))
      else 0 := by
  unfold e11F
  simp only [max_def, min_def]
  split_ifs <;> first
    | linarith
    | (exfalso; linarith)
    | (have e : b = p := (by linarith); subst e; linarith)
    | (have e : a = q := (by linarith); subst e; linarith)
    | (have e : a = p := (by linarith); subst e; linarith)
    | (have e : b = q := (by linarith); subst e; linarith)

lemma e11_cost (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ) (ψ : Equiv.Perm (Fin (n + 1)))
    (i j : Fin (n + 1)) :
    interchangeCost f g A B ψ i j =
      c f g A B i (ψ j) + c f g A B j (ψ i) - c f g A B i (ψ i) - c f g A B j (ψ j) := by
  unfold interchangeCost cost
  by_cases hij : i = j
  · subst hij; simp [alpha]
  · rw [← Finset.sum_sub_distrib]
    rw [← Finset.sum_subset (Finset.subset_univ ({i, j} : Finset (Fin (n+1))))]
    · rw [Finset.sum_pair hij]
      simp [alpha, Equiv.swap_apply_left, Equiv.swap_apply_right]
      ring
    · intro x _ hx
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
      simp [alpha, Equiv.swap_apply_of_ne_of_ne hx.1 hx.2]

theorem eq_11_core {n : ℕ}
    (f g : ℝ → ℝ) (hf : MeasureTheory.LocallyIntegrable f) (hg : MeasureTheory.LocallyIntegrable g)
    (hfg : ∀ x, 0 ≤ f x + g x) (A B : Fin (n + 1) → ℝ)
    (ψ : Equiv.Perm (Fin (n + 1))) (i j : Fin (n + 1))
    (hBij : B i ≤ B j) (hAij : A (ψ i) ≤ A (ψ j)) :
    interchangeCost f g A B ψ i j =
      ∫ x in Set.Icc (B i) (B j) ∩ Set.Icc (A (ψ i)) (A (ψ j)), (f x + g x) := by
  rw [e11_cost, e11_c f g hf hg, e11_c f g hf hg, e11_c f g hf hg, e11_c f g hf hg]
  set φ : ℝ → ℝ := fun t => ∫ x in (0:ℝ)..t, f x
  set γ : ℝ → ℝ := fun t => ∫ x in (0:ℝ)..t, g x
  rw [e11_alg φ γ _ _ _ _ hBij hAij, Set.Icc_inter_Icc]
  split_ifs with h
  · have h1 : φ (min (B j) (A (ψ j))) - φ (max (B i) (A (ψ i))) =
        ∫ x in (max (B i) (A (ψ i)))..(min (B j) (A (ψ j))), f x :=
      intervalIntegral.integral_interval_sub_left (e11_ii f hf _ _) (e11_ii f hf _ _)
    have h2 : γ (min (B j) (A (ψ j))) - γ (max (B i) (A (ψ i))) =
        ∫ x in (max (B i) (A (ψ i)))..(min (B j) (A (ψ j))), g x :=
      intervalIntegral.integral_interval_sub_left (e11_ii g hg _ _) (e11_ii g hg _ _)
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h,
      intervalIntegral.integral_add (e11_ii f hf _ _) (e11_ii g hg _ _)]
    linarith
  · rw [Set.Icc_eq_empty h]; simp


def L5Type1 (A B : Fin (n+1) → ℝ) (φ : Equiv.Perm (Fin (n+1))) (p : Fin (n+1)) : Prop :=
  B p ≤ A (φ p)

def L5Good (A B : Fin (n+1) → ℝ) (φ ψ : Equiv.Perm (Fin (n+1))) (q : Fin n) : Prop :=
  A (ψ q.castSucc) ≤ A (ψ q.succ) ∧ ∀ x, B q.castSucc ≤ x → x ≤ B q.succ →
    (A (ψ q.castSucc) ≤ x ↔ A (φ q.castSucc) ≤ x) ∧ (x ≤ A (ψ q.succ) ↔ x ≤ A (φ q.succ))

lemma l5_step (f g : ℝ → ℝ) (hf : LocallyIntegrable f) (hg : LocallyIntegrable g)
    (hfg : ∀ x, 0 ≤ f x + g x) (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : RanksA A φ) (ψ : Equiv.Perm (Fin (n + 1))) (q : Fin n)
    (h : L5Good A B φ ψ q) :
    interchangeCost f g A B ψ q.castSucc q.succ = interchangeCost f g A B φ q.castSucc q.succ := by
  rw [eq_11_core f g hf hg hfg A B ψ _ _ (hB (Fin.castSucc_lt_succ).le) h.1,
    eq_11_core f g hf hg hfg A B φ _ _ (hB (Fin.castSucc_lt_succ).le)
      (hφ (Fin.castSucc_lt_succ).le)]
  have hset : Set.Icc (B q.castSucc) (B q.succ) ∩ Set.Icc (A (ψ q.castSucc)) (A (ψ q.succ)) =
      Set.Icc (B q.castSucc) (B q.succ) ∩ Set.Icc (A (φ q.castSucc)) (A (φ q.succ)) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      have := h.2 x h1 h2
      exact ⟨⟨h1, h2⟩, this.1.mp h3, this.2.mp h4⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      have := h.2 x h1 h2
      exact ⟨⟨h1, h2⟩, this.1.mpr h3, this.2.mpr h4⟩
  rw [hset]

def L5GoodList (A B : Fin (n+1) → ℝ) (φ : Equiv.Perm (Fin (n+1))) :
    Equiv.Perm (Fin (n+1)) → List (Fin n) → Prop
  | _, [] => True
  | ψ, q :: l => L5Good A B φ ψ q ∧ L5GoodList A B φ (ψ * alpha q.castSucc q.succ) l

lemma l5_run (f g : ℝ → ℝ) (hf : LocallyIntegrable f) (hg : LocallyIntegrable g)
    (hfg : ∀ x, 0 ≤ f x + g x) (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : RanksA A φ) :
    ∀ (l : List (Fin n)) (ψ : Equiv.Perm (Fin (n+1))), L5GoodList A B φ ψ l →
      cost f g A B (applyAdj ψ l) = cost f g A B ψ +
        (l.map fun q => interchangeCost f g A B φ q.castSucc q.succ).sum := by
  intro l
  induction l with
  | nil => intro ψ _; simp [applyAdj]
  | cons q l ih =>
    rintro ψ ⟨h1, h2⟩
    have e : applyAdj ψ (q :: l) = applyAdj (ψ * alpha q.castSucc q.succ) l := rfl
    rw [e, ih _ h2]
    have hc : cost f g A B (ψ * alpha q.castSucc q.succ) =
        cost f g A B ψ + interchangeCost f g A B ψ q.castSucc q.succ := by
      unfold interchangeCost; ring
    rw [hc, l5_step f g hf hg hfg A B hB φ hφ ψ q h1]
    simp only [List.map_cons, List.sum_cons]
    ring

lemma l5_append (A B : Fin (n+1) → ℝ) (φ : Equiv.Perm (Fin (n+1))) :
    ∀ (l1 l2 : List (Fin n)) (ψ : Equiv.Perm (Fin (n+1))), L5GoodList A B φ ψ l1 →
      L5GoodList A B φ (applyAdj ψ l1) l2 → L5GoodList A B φ ψ (l1 ++ l2) := by
  intro l1
  induction l1 with
  | nil => intro l2 ψ _ h; simpa [applyAdj] using h
  | cons q l ih =>
    rintro l2 ψ ⟨h1, h2⟩ h3
    exact ⟨h1, ih l2 _ h2 h3⟩

lemma l5_sv (φ ψ : Equiv.Perm (Fin (n+1))) (p : Fin n) (x : Fin (n+1)) :
    φ.symm ((ψ * alpha p.castSucc p.succ) x) =
      if x = p.castSucc then φ.symm (ψ p.succ)
      else if x = p.succ then φ.symm (ψ p.castSucc) else φ.symm (ψ x) := by
  simp only [alpha, Equiv.Perm.mul_apply]
  by_cases h1 : x = p.castSucc
  · subst h1; simp
  by_cases h2 : x = p.succ
  · subst h2; simp [h1]
  · simp [h1, h2, Equiv.swap_apply_of_ne_of_ne h1 h2]

lemma l5_cs_eq (q p : Fin n) : q.castSucc = p.succ ↔ q.val = p.val + 1 := by
  simp [Fin.ext_iff]

lemma l5_sc_eq (q p : Fin n) : q.succ = p.castSucc ↔ q.val + 1 = p.val := by
  simp [Fin.ext_iff]

lemma l5_cc_eq (q p : Fin n) : q.castSucc = p.castSucc ↔ q = p := Fin.castSucc_inj

lemma l5_ss_eq (q p : Fin n) : q.succ = p.succ ↔ q = p := Fin.succ_inj

lemma l5_cs_le (q : Fin n) : q.castSucc ≤ q.succ := (Fin.castSucc_lt_succ).le

/-- invariants -/
def L5PB (A B : Fin (n+1) → ℝ) (φ ψ : Equiv.Perm (Fin (n+1))) (q : Fin n) : Prop :=
  φ.symm (ψ q.succ) = q.succ ∨ (L5Type1 A B φ q.succ ∧ q.succ ≤ φ.symm (ψ q.succ))

lemma l5_PB_le (A B : Fin (n+1) → ℝ) (φ ψ : Equiv.Perm (Fin (n+1))) (q : Fin n)
    (h : L5PB A B φ ψ q) : q.succ ≤ φ.symm (ψ q.succ) := by
  rcases h with h | h
  · exact h.ge
  · exact h.2

lemma l5_phase1 (A B : Fin (n+1) → ℝ) (φ : Equiv.Perm (Fin (n+1))) (hφ : RanksA A φ)
    (T2 : Finset (Fin n)) :
    ∀ (U : List (Fin n)) (ψ : Equiv.Perm (Fin (n+1))),
      U.Pairwise (· > ·) → (∀ q ∈ U, L5Type1 A B φ q.castSucc) → (∀ q ∈ U, q ∉ T2) →
      (∀ q ∈ U, φ.symm (ψ q.castSucc) = q.castSucc ∧ L5PB A B φ ψ q) →
      (∀ q ∈ T2, φ.symm (ψ q.castSucc) ≤ q.castSucc ∧ L5PB A B φ ψ q) →
      L5GoodList A B φ ψ U ∧
        (∀ q ∈ T2, φ.symm (applyAdj ψ U q.castSucc) ≤ q.castSucc ∧
          L5PB A B φ (applyAdj ψ U) q) := by
  intro U
  induction U with
  | nil => intro ψ _ _ _ _ h; exact ⟨trivial, h⟩
  | cons p U ih =>
    intro ψ hpw hty hn2 hinv hT2
    rw [List.pairwise_cons] at hpw
    obtain ⟨hp1, hp2⟩ := hpw
    have hpU := hinv p (List.mem_cons_self)
    have hpty := hty p (List.mem_cons_self)
    have hpn : p ∉ T2 := hn2 p (List.mem_cons_self)
    set ψ' := ψ * alpha p.castSucc p.succ with hψ'
    have hc' : φ.symm (ψ' p.castSucc) = φ.symm (ψ p.succ) := by rw [hψ', l5_sv]; simp
    have hs' : φ.symm (ψ' p.succ) = p.castSucc := by
      rw [hψ', l5_sv]
      have : p.succ ≠ p.castSucc := (Fin.castSucc_lt_succ).ne'
      simp [this, hpU.1]
    have hother : ∀ x, x ≠ p.castSucc → x ≠ p.succ → φ.symm (ψ' x) = φ.symm (ψ x) := by
      intro x h1 h2; rw [hψ', l5_sv]; simp [h1, h2]
    have hpsle : p.succ ≤ φ.symm (ψ p.succ) := l5_PB_le A B φ ψ p hpU.2
    -- good
    have hgood : L5Good A B φ ψ p := by
      have hψc : ψ p.castSucc = φ p.castSucc := by
        have := hpU.1
        rw [Equiv.symm_apply_eq] at this; exact this
      have hψs : ψ p.succ = φ (φ.symm (ψ p.succ)) := by simp
      have hmono := hφ hpsle
      simp only [Function.comp] at hmono
      have hmono2 := hφ (l5_cs_le p)
      simp only [Function.comp] at hmono2
      refine ⟨?_, ?_⟩
      · rw [hψc, hψs]; exact hmono2.trans hmono
      · intro x hx1 hx2
        refine ⟨by rw [hψc], ?_⟩
        rcases hpU.2 with h | h
        · have : ψ p.succ = φ p.succ := by
            rw [Equiv.symm_apply_eq] at h; exact h
          rw [this]
        · have hb : B p.succ ≤ A (φ p.succ) := h.1
          constructor
          · intro _; linarith
          · intro _
            rw [hψs]
            linarith
    have hnew : (∀ q ∈ U, φ.symm (ψ' q.castSucc) = q.castSucc ∧ L5PB A B φ ψ' q) ∧
        (∀ q ∈ T2, φ.symm (ψ' q.castSucc) ≤ q.castSucc ∧ L5PB A B φ ψ' q) := by
      constructor
      · intro q hq
        have hqp := hp1 q hq
        have hqv : q.val < p.val := hqp
        have hqU := hinv q (List.mem_cons_of_mem _ hq)
        have c1 : q.castSucc ≠ p.castSucc := by
          intro h; rw [l5_cc_eq] at h; subst h; exact lt_irrefl _ hqp
        have c2 : q.castSucc ≠ p.succ := by
          intro h; rw [l5_cs_eq] at h; omega
        refine ⟨by rw [hother _ c1 c2]; exact hqU.1, ?_⟩
        unfold L5PB
        by_cases d1 : q.succ = p.castSucc
        · rw [d1, hc']
          right
          refine ⟨?_, ?_⟩
          · exact hpty
          · exact (l5_cs_le p).trans hpsle
        · have d2 : q.succ ≠ p.succ := by
            intro h; rw [l5_ss_eq] at h; subst h; exact lt_irrefl _ hqp
          rw [hother _ d1 d2]
          exact hqU.2
      · intro q hq
        have hqp : q ≠ p := fun h => hpn (h ▸ hq)
        have hqT := hT2 q hq
        refine ⟨?_, ?_⟩
        · by_cases d1 : q.castSucc = p.castSucc
          · exact absurd ((l5_cc_eq q p).mp d1) hqp
          · by_cases d2 : q.castSucc = p.succ
            · rw [d2, hs']; exact l5_cs_le p
            · rw [hother _ d1 d2]; exact hqT.1
        · unfold L5PB
          by_cases d1 : q.succ = p.castSucc
          · rw [d1, hc']
            right
            refine ⟨?_, ?_⟩
            · exact hpty
            · exact (l5_cs_le p).trans hpsle
          · have d2 : q.succ ≠ p.succ := fun h => hqp ((l5_ss_eq q p).mp h)
            rw [hother _ d1 d2]
            exact hqT.2
    obtain ⟨ih1, ih2⟩ := ih ψ' hp2 (fun q hq => hty q (List.mem_cons_of_mem _ hq))
      (fun q hq => hn2 q (List.mem_cons_of_mem _ hq)) hnew.1 hnew.2
    exact ⟨⟨hgood, ih1⟩, ih2⟩

lemma l5_phase2 (A B : Fin (n+1) → ℝ) (φ : Equiv.Perm (Fin (n+1))) (hφ : RanksA A φ) :
    ∀ (V : List (Fin n)) (ψ : Equiv.Perm (Fin (n+1))),
      V.Pairwise (· < ·) → (∀ q ∈ V, ¬ L5Type1 A B φ q.castSucc) →
      (∀ q ∈ V, φ.symm (ψ q.castSucc) ≤ q.castSucc ∧ L5PB A B φ ψ q) →
      L5GoodList A B φ ψ V := by
  intro V
  induction V with
  | nil => intro ψ _ _ _; trivial
  | cons p V ih =>
    intro ψ hpw hty hinv
    rw [List.pairwise_cons] at hpw
    obtain ⟨hp1, hp2⟩ := hpw
    have hpU := hinv p (List.mem_cons_self)
    have hpty := hty p (List.mem_cons_self)
    set ψ' := ψ * alpha p.castSucc p.succ with hψ'
    have hs' : φ.symm (ψ' p.succ) = φ.symm (ψ p.castSucc) := by
      rw [hψ', l5_sv]
      have : p.succ ≠ p.castSucc := (Fin.castSucc_lt_succ).ne'
      simp [this]
    have hother : ∀ x, x ≠ p.castSucc → x ≠ p.succ → φ.symm (ψ' x) = φ.symm (ψ x) := by
      intro x h1 h2; rw [hψ', l5_sv]; simp [h1, h2]
    have hpsle : p.succ ≤ φ.symm (ψ p.succ) := l5_PB_le A B φ ψ p hpU.2
    have hgood : L5Good A B φ ψ p := by
      have hψc : ψ p.castSucc = φ (φ.symm (ψ p.castSucc)) := by simp
      have hψs : ψ p.succ = φ (φ.symm (ψ p.succ)) := by simp
      have hmono := hφ hpsle
      simp only [Function.comp] at hmono
      have hmono2 := hφ (l5_cs_le p)
      simp only [Function.comp] at hmono2
      have hmono3 := hφ hpU.1
      simp only [Function.comp] at hmono3
      have hlt : A (φ p.castSucc) < B p.castSucc := lt_of_not_ge hpty
      refine ⟨?_, ?_⟩
      · rw [hψc, hψs]; exact hmono3.trans (hmono2.trans hmono)
      · intro x hx1 hx2
        refine ⟨?_, ?_⟩
        · constructor
          · intro _; linarith
          · intro _
            rw [hψc]; linarith
        · rcases hpU.2 with h | h
          · have : ψ p.succ = φ p.succ := by
              rw [Equiv.symm_apply_eq] at h; exact h
            rw [this]
          · have hb : B p.succ ≤ A (φ p.succ) := h.1
            constructor
            · intro _; linarith
            · intro _
              rw [hψs]
              linarith
    refine ⟨hgood, ih ψ' hp2 (fun q hq => hty q (List.mem_cons_of_mem _ hq)) ?_⟩
    intro q hq
    have hqp := hp1 q hq
    have hqv : p.val < q.val := hqp
    have hqU := hinv q (List.mem_cons_of_mem _ hq)
    refine ⟨?_, ?_⟩
    · by_cases d2 : q.castSucc = p.succ
      · rw [d2, hs']; exact hpU.1.trans (l5_cs_le p)
      · have d1 : q.castSucc ≠ p.castSucc := by
          intro h; rw [l5_cc_eq] at h; subst h; exact lt_irrefl _ hqp
        rw [hother _ d1 d2]; exact hqU.1
    · unfold L5PB
      have d1 : q.succ ≠ p.castSucc := by
        intro h; rw [l5_sc_eq] at h; omega
      have d2 : q.succ ≠ p.succ := by
        intro h; rw [l5_ss_eq] at h; subst h; exact lt_irrefl _ hqp
      rw [hother _ d1 d2]
      exact hqU.2

lemma l5_sort_lt (T : Finset (Fin n)) : (T.sort (· ≤ ·)).Pairwise (· < ·) := by
  have h1 := Finset.pairwise_sort T (· ≤ ·)
  have h2 : (T.sort (· ≤ ·)).Pairwise (· ≠ ·) := Finset.sort_nodup T (· ≤ ·)
  exact (h1.and h2).imp (fun h => lt_of_le_of_ne h.1 h.2)

lemma l5_exec_facts (A B : Fin (n + 1) → ℝ) (φ : Equiv.Perm (Fin (n + 1))) (T : Finset (Fin n)) :
    (execOrder A B φ T).Nodup ∧ (execOrder A B φ T).toFinset = T := by
  unfold execOrder
  set T1 := T.filter fun q => B q.castSucc ≤ A (φ q.castSucc) with hT1
  set T2 := T.filter fun q => ¬ B q.castSucc ≤ A (φ q.castSucc) with hT2
  constructor
  · rw [List.nodup_append]
    refine ⟨?_, Finset.sort_nodup T2 _, ?_⟩
    · rw [List.nodup_reverse]; exact Finset.sort_nodup T1 _
    · intro a ha b hb hab
      subst hab
      rw [List.mem_reverse, Finset.mem_sort] at ha
      rw [Finset.mem_sort] at hb
      simp only [hT1, hT2, Finset.mem_filter] at ha hb
      exact hb.2 ha.2
  · rw [List.toFinset_append, List.toFinset_reverse, Finset.sort_toFinset, Finset.sort_toFinset]
    exact Finset.filter_union_filter_not_eq _ _

theorem lemma_5_core {n : ℕ}
    (f g : ℝ → ℝ) (hf : MeasureTheory.LocallyIntegrable f) (hg : MeasureTheory.LocallyIntegrable g)
    (hfg : ∀ x, 0 ≤ f x + g x) (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : RanksA A φ)
    (T : Finset (Fin n)) :
    cost f g A B (applyAdj φ (execOrder A B φ T)) =
      cost f g A B φ + adjTreeCost f g A B φ T := by
  set T1 := T.filter fun q => B q.castSucc ≤ A (φ q.castSucc) with hT1
  set T2 := T.filter fun q => ¬ B q.castSucc ≤ A (φ q.castSucc) with hT2
  have hexec : execOrder A B φ T = (T1.sort (· ≤ ·)).reverse ++ T2.sort (· ≤ ·) := rfl
  have hU : ((T1.sort (· ≤ ·)).reverse).Pairwise (· > ·) := by
    rw [List.pairwise_reverse]
    exact l5_sort_lt T1
  have hV : (T2.sort (· ≤ ·)).Pairwise (· < ·) := l5_sort_lt T2
  have hP1 := l5_phase1 A B φ hφ T2 ((T1.sort (· ≤ ·)).reverse) φ hU
    (by
      intro q hq
      rw [List.mem_reverse, Finset.mem_sort] at hq
      exact (Finset.mem_filter.mp hq).2)
    (by
      intro q hq hq2
      rw [List.mem_reverse, Finset.mem_sort] at hq
      exact (Finset.mem_filter.mp hq2).2 (Finset.mem_filter.mp hq).2)
    (by
      intro q _
      refine ⟨by simp, ?_⟩
      left; simp)
    (by
      intro q _
      refine ⟨by simp, ?_⟩
      left; simp)
  have hP2 := l5_phase2 A B φ hφ (T2.sort (· ≤ ·)) _ hV
    (by
      intro q hq
      rw [Finset.mem_sort] at hq
      exact (Finset.mem_filter.mp hq).2)
    (by
      intro q hq
      rw [Finset.mem_sort] at hq
      exact hP1.2 q hq)
  have hgood : L5GoodList A B φ φ (execOrder A B φ T) := by
    rw [hexec]
    exact l5_append A B φ _ _ φ hP1.1 hP2
  rw [l5_run f g hf hg hfg A B hB φ hφ _ φ hgood]
  obtain ⟨hnd, hts⟩ := l5_exec_facts A B φ T
  unfold adjTreeCost
  congr 1
  rw [← List.sum_toFinset _ hnd, hts]


theorem theorem_3_core {n : ℕ}
    (f g : ℝ → ℝ) (hf : MeasureTheory.LocallyIntegrable f) (hg : MeasureTheory.LocallyIntegrable g)
    (hfg : ∀ x, 0 ≤ f x + g x) (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : RanksA A φ)
    (T : Finset (Fin n)) (hT : IsMinCostAdjTree f g A B φ T) :
    IsTour (psiStar A B φ T) ∧
      cost f g A B (psiStar A B φ T) = cost f g A B φ + adjTreeCost f g A B φ T := by
  refine ⟨?_, lemma_5_core f g hf hg hfg A B hB φ hφ T⟩
  obtain ⟨hnd, hts⟩ := l5_exec_facts A B φ T
  have hinj : Function.Injective (adjArc : Fin n → Fin (n+1) × Fin (n+1)) := by
    intro a b h
    have := congrArg Prod.fst h
    exact Fin.castSucc_injective _ this
  have hL : ((execOrder A B φ T).map adjArc).Nodup := hnd.map hinj
  have hLs : ((execOrder A B φ T).map adjArc).toFinset = adjArcs T := by
    have hmem : ∀ q, q ∈ execOrder A B φ T ↔ q ∈ T := fun q => by
      rw [← List.mem_toFinset, hts]
    ext e
    simp only [List.mem_toFinset, List.mem_map, adjArcs, Finset.mem_image, hmem]
  have hsp : IsSpanningTree φ ((execOrder A B φ T).map adjArc).toFinset := by
    rw [hLs]; exact hT.1
  have := theorem_2_core φ _ hL hsp
  unfold psiStar applyAdj
  rw [List.foldl_map] at this
  exact this

lemma cnt_int_ind (f : ℝ → ℝ) (hf : LocallyIntegrable f) (a b : ℝ) :
    Integrable ((Set.Ico a b).indicator f) :=
  (integrable_indicator_iff measurableSet_Ico).mpr
    ((hf.integrableOn_isCompact isCompact_Icc).mono_set Set.Ico_subset_Icc_self)

lemma cnt_ico (f : ℝ → ℝ) (hf : LocallyIntegrable f) (a b : ℝ) (h : a ≤ b) :
    ∫ x, (Set.Ico a b).indicator f x = ∫ x in a..b, f x := by
  rw [integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioo,
    ← integral_Ioc_eq_integral_Ioo, intervalIntegral.integral_of_le h]

/-- the integrand of the cost of one changeover -/
noncomputable def cntT (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ) (i j : Fin (n + 1)) (x : ℝ) : ℝ :=
  (Set.Ico (B i) (A j)).indicator f x + (Set.Ico (A j) (B i)).indicator g x

lemma cnt_T_int (f g : ℝ → ℝ) (hf : LocallyIntegrable f) (hg : LocallyIntegrable g)
    (A B : Fin (n + 1) → ℝ) (i j : Fin (n + 1)) : Integrable (cntT f g A B i j) :=
  (cnt_int_ind f hf _ _).add (cnt_int_ind g hg _ _)

lemma cnt_c (f g : ℝ → ℝ) (hf : LocallyIntegrable f) (hg : LocallyIntegrable g)
    (A B : Fin (n + 1) → ℝ) (i j : Fin (n + 1)) :
    c f g A B i j = ∫ x, cntT f g A B i j x := by
  unfold cntT
  rw [integral_add (cnt_int_ind f hf _ _) (cnt_int_ind g hg _ _)]
  unfold c
  split_ifs with h
  · have : Set.Ico (A j) (B i) = ∅ := Set.Ico_eq_empty (not_lt.mpr h)
    rw [this, cnt_ico f hf _ _ h]
    simp
  · have h' : A j ≤ B i := (not_le.mp h).le
    have : Set.Ico (B i) (A j) = ∅ := Set.Ico_eq_empty (not_lt.mpr h')
    rw [this, cnt_ico g hg _ _ h']
    simp

noncomputable def cntW (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ) (ψ : Equiv.Perm (Fin (n + 1)))
    (x : ℝ) : ℝ := ∑ i, cntT f g A B i (ψ i) x

lemma cnt_W_int (f g : ℝ → ℝ) (hf : LocallyIntegrable f) (hg : LocallyIntegrable g)
    (A B : Fin (n + 1) → ℝ) (ψ : Equiv.Perm (Fin (n + 1))) : Integrable (cntW f g A B ψ) := by
  unfold cntW
  exact integrable_finsetSum _ (fun i _ => cnt_T_int f g hf hg A B i (ψ i))

lemma cnt_cost (f g : ℝ → ℝ) (hf : LocallyIntegrable f) (hg : LocallyIntegrable g)
    (A B : Fin (n + 1) → ℝ) (ψ : Equiv.Perm (Fin (n + 1))) :
    cost f g A B ψ = ∫ x, cntW f g A B ψ x := by
  unfold cost cntW
  rw [integral_finsetSum _ (fun i _ => cnt_T_int f g hf hg A B i (ψ i))]
  exact Finset.sum_congr rfl (fun i _ => cnt_c f g hf hg A B i (ψ i))

/-- counts -/
noncomputable def cntNf (A B : Fin (n + 1) → ℝ) (ψ : Equiv.Perm (Fin (n + 1))) (x : ℝ) : ℝ :=
  ∑ i, if B i ≤ x ∧ x < A (ψ i) then (1:ℝ) else 0

noncomputable def cntNg (A B : Fin (n + 1) → ℝ) (ψ : Equiv.Perm (Fin (n + 1))) (x : ℝ) : ℝ :=
  ∑ i, if A (ψ i) ≤ x ∧ x < B i then (1:ℝ) else 0

noncomputable def cntD (A B : Fin (n + 1) → ℝ) (x : ℝ) : ℝ :=
  (∑ i, if B i ≤ x then (1:ℝ) else 0) - ∑ i, if A i ≤ x then (1:ℝ) else 0

lemma cntNf_nonneg (A B : Fin (n + 1) → ℝ) (ψ : Equiv.Perm (Fin (n + 1))) (x : ℝ) :
    0 ≤ cntNf A B ψ x :=
  Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)

lemma cntNg_nonneg (A B : Fin (n + 1) → ℝ) (ψ : Equiv.Perm (Fin (n + 1))) (x : ℝ) :
    0 ≤ cntNg A B ψ x :=
  Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)

lemma cnt_W_eq (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ) (ψ : Equiv.Perm (Fin (n + 1))) (x : ℝ) :
    cntW f g A B ψ x = cntNf A B ψ x * f x + cntNg A B ψ x * g x := by
  unfold cntW cntNf cntNg cntT
  rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Set.indicator_apply, Set.mem_Ico]
  split_ifs <;> simp

lemma cnt_diff (A B : Fin (n + 1) → ℝ) (ψ : Equiv.Perm (Fin (n + 1))) (x : ℝ) :
    cntNf A B ψ x - cntNg A B ψ x = cntD A B x := by
  unfold cntNf cntNg cntD
  rw [← Finset.sum_sub_distrib]
  have h2 : ∑ i, (if A (ψ i) ≤ x then (1:ℝ) else 0) = ∑ i, if A i ≤ x then (1:ℝ) else 0 :=
    Equiv.sum_comp ψ (fun j => if A j ≤ x then (1:ℝ) else 0)
  rw [← h2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  generalize B i = b
  generalize A (ψ i) = a
  rcases le_or_gt b x with hb | hb <;> rcases le_or_gt a x with ha | ha <;>
    simp [hb, ha, not_lt_of_ge, not_le_of_gt, le_of_lt]

lemma cnt_sorted (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : Monotone (A ∘ φ)) (x : ℝ) :
    cntNf A B φ x = 0 ∨ cntNg A B φ x = 0 := by
  by_contra hcon
  push Not at hcon
  have h1 : ∃ i, B i ≤ x ∧ x < A (φ i) := by
    by_contra hh
    push Not at hh
    apply hcon.1
    exact Finset.sum_eq_zero (fun i _ => by
      rw [if_neg]; intro h; exact absurd h.2 (not_lt.mpr (hh i h.1)))
  have h2 : ∃ j, A (φ j) ≤ x ∧ x < B j := by
    by_contra hh
    push Not at hh
    apply hcon.2
    exact Finset.sum_eq_zero (fun i _ => by
      rw [if_neg]; intro h; exact absurd h.2 (not_lt.mpr (hh i h.1)))
  obtain ⟨i, hi1, hi2⟩ := h1
  obtain ⟨j, hj1, hj2⟩ := h2
  have hij : i < j := by
    by_contra h; push Not at h
    have := hB h; linarith
  have hji : j < i := by
    by_contra h; push Not at h
    have := hφ h; simp only [Function.comp] at this; linarith
  exact lt_asymm hij hji

lemma cnt_Ng_le (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : Monotone (A ∘ φ)) (ψ : Equiv.Perm (Fin (n + 1)))
    (x : ℝ) : cntNg A B φ x ≤ cntNg A B ψ x := by
  have h1 := cnt_diff A B φ x
  have h2 := cnt_diff A B ψ x
  have := cnt_sorted A B hB φ hφ x
  have := cntNf_nonneg A B ψ x
  have := cntNg_nonneg A B ψ x
  have := cntNf_nonneg A B φ x
  have := cntNg_nonneg A B φ x
  rcases cnt_sorted A B hB φ hφ x with h | h <;> linarith

lemma cnt_W_sub (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ) (ψ φ : Equiv.Perm (Fin (n + 1))) (x : ℝ) :
    cntW f g A B ψ x - cntW f g A B φ x =
      (cntNg A B ψ x - cntNg A B φ x) * (f x + g x) := by
  rw [cnt_W_eq, cnt_W_eq]
  have h1 := cnt_diff A B φ x
  have h2 := cnt_diff A B ψ x
  have e1 : cntNf A B ψ x = cntNg A B ψ x + cntD A B x := by linarith
  have e2 : cntNf A B φ x = cntNg A B φ x + cntD A B x := by linarith
  rw [e1, e2]; ring


lemma st_meas_P (A B : Fin (n + 1) → ℝ) (φ : Equiv.Perm (Fin (n + 1))) :
    MeasurableSet (P A B φ) := by
  unfold P Pq
  exact MeasurableSet.iUnion (fun q => measurableSet_Icc.inter measurableSet_Icc)

lemma st_int_ind (f : ℝ → ℝ) (hf : LocallyIntegrable f) (a b : ℝ) (S : Set ℝ)
    (hS : MeasurableSet S) :
    Integrable ((Set.Icc a b ∩ S).indicator f) :=
  (integrable_indicator_iff (measurableSet_Icc.inter hS)).mpr
    ((hf.integrableOn_isCompact isCompact_Icc).mono_set Set.inter_subset_left)

noncomputable def stT (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ) (φ : Equiv.Perm (Fin (n + 1)))
    (i j : Fin (n + 1)) (x : ℝ) : ℝ :=
  (Set.Icc (B i) (A j) ∩ P A B φ).indicator f x + (Set.Icc (A j) (B i) ∩ P A B φ).indicator g x

lemma st_T_int (f g : ℝ → ℝ) (hf : LocallyIntegrable f) (hg : LocallyIntegrable g)
    (A B : Fin (n + 1) → ℝ) (φ : Equiv.Perm (Fin (n + 1))) (i j : Fin (n + 1)) :
    Integrable (stT f g A B φ i j) :=
  (st_int_ind f hf _ _ _ (st_meas_P A B φ)).add (st_int_ind g hg _ _ _ (st_meas_P A B φ))

lemma st_cStar (f g : ℝ → ℝ) (hf : LocallyIntegrable f) (hg : LocallyIntegrable g)
    (A B : Fin (n + 1) → ℝ) (φ : Equiv.Perm (Fin (n + 1))) (i j : Fin (n + 1)) :
    cStar f g A B φ i j = ∫ x, stT f g A B φ i j x := by
  unfold stT cStar
  rw [integral_add (st_int_ind f hf _ _ _ (st_meas_P A B φ))
    (st_int_ind g hg _ _ _ (st_meas_P A B φ)),
    integral_indicator (measurableSet_Icc.inter (st_meas_P A B φ)),
    integral_indicator (measurableSet_Icc.inter (st_meas_P A B φ))]

noncomputable def stW (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ) (φ ψ : Equiv.Perm (Fin (n + 1)))
    (x : ℝ) : ℝ := ∑ i, stT f g A B φ i (ψ i) x

lemma st_W_int (f g : ℝ → ℝ) (hf : LocallyIntegrable f) (hg : LocallyIntegrable g)
    (A B : Fin (n + 1) → ℝ) (φ ψ : Equiv.Perm (Fin (n + 1))) : Integrable (stW f g A B φ ψ) := by
  unfold stW
  exact integrable_finsetSum _ (fun i _ => st_T_int f g hf hg A B φ i (ψ i))

lemma st_costStar (f g : ℝ → ℝ) (hf : LocallyIntegrable f) (hg : LocallyIntegrable g)
    (A B : Fin (n + 1) → ℝ) (φ ψ : Equiv.Perm (Fin (n + 1))) :
    costStar f g A B φ ψ = ∫ x, stW f g A B φ ψ x := by
  unfold costStar stW
  rw [integral_finsetSum _ (fun i _ => st_T_int f g hf hg A B φ i (ψ i))]
  exact Finset.sum_congr rfl (fun i _ => st_cStar f g hf hg A B φ i (ψ i))

lemma st_out (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ) (φ ψ : Equiv.Perm (Fin (n + 1))) (x : ℝ)
    (hx : x ∉ P A B φ) : stW f g A B φ ψ x = 0 := by
  unfold stW stT
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [Set.indicator_of_notMem (fun h => hx h.2), Set.indicator_of_notMem (fun h => hx h.2)]
  simp

lemma st_in (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ) (φ ψ : Equiv.Perm (Fin (n + 1))) (x : ℝ)
    (hx : x ∈ P A B φ) (hxA : ∀ i, x ≠ A i) (hxB : ∀ i, x ≠ B i) :
    stW f g A B φ ψ x = cntW f g A B ψ x := by
  unfold stW cntW stT cntT
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have e1 : x ∈ Set.Icc (B i) (A (ψ i)) ∩ P A B φ ↔ x ∈ Set.Ico (B i) (A (ψ i)) := by
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ico]
    constructor
    · rintro ⟨⟨h1, h2⟩, _⟩; exact ⟨h1, lt_of_le_of_ne h2 (hxA _)⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.le⟩, hx⟩
  have e2 : x ∈ Set.Icc (A (ψ i)) (B i) ∩ P A B φ ↔ x ∈ Set.Ico (A (ψ i)) (B i) := by
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ico]
    constructor
    · rintro ⟨⟨h1, h2⟩, _⟩; exact ⟨h1, lt_of_le_of_ne h2 (hxB _)⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.le⟩, hx⟩
  have key : ∀ (h : ℝ → ℝ) (S T : Set ℝ), (x ∈ S ↔ x ∈ T) → S.indicator h x = T.indicator h x := by
    intro h S T hST
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hST.mp hx)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h' => hx (hST.mpr h'))]
  rw [key f _ _ e1, key g _ _ e2]

lemma st_phi_zero (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : Monotone (A ∘ φ)) (x : ℝ)
    (hx : x ∈ P A B φ) (hxA : ∀ i, x ≠ A i) (hxB : ∀ i, x ≠ B i) :
    cntW f g A B φ x = 0 := by
  obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hx
  simp only [Pq, Set.mem_inter_iff, Set.mem_Icc] at hq
  obtain ⟨⟨hq1, hq2⟩, hq3, hq4⟩ := hq
  have hNf : cntNf A B φ x = 0 := by
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [if_neg]
    rintro ⟨h1, h2⟩
    have hlt : x < B q.succ := lt_of_le_of_ne hq2 (hxB _)
    have hi : i ≤ q.castSucc := by
      by_contra hc
      push Not at hc
      have : q.succ ≤ i := Fin.castSucc_lt_iff_succ_le.mp hc
      have := hB this
      linarith
    have := hφ hi
    simp only [Function.comp] at this
    linarith
  have hNg : cntNg A B φ x = 0 := by
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [if_neg]
    rintro ⟨h1, h2⟩
    have hi : q.succ ≤ i := by
      by_contra hc
      push Not at hc
      have hc' : i ≤ q.castSucc := Fin.le_castSucc_iff.mpr hc
      have := hB hc'
      linarith
    have := hφ hi
    simp only [Function.comp] at this
    exact hxA _ (le_antisymm hq4 (by linarith))
  rw [cnt_W_eq, hNf, hNg]; simp

theorem theorem_4_core {n : ℕ}
    (f g : ℝ → ℝ) (hf : MeasureTheory.LocallyIntegrable f) (hg : MeasureTheory.LocallyIntegrable g)
    (hfg : ∀ x, 0 ≤ f x + g x) (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : RanksA A φ) :
    ∀ ψ : Equiv.Perm (Fin (n + 1)),
      cost f g A B φ + costStar f g A B φ ψ ≤ cost f g A B ψ := by
  intro ψ
  rw [cnt_cost f g hf hg, cnt_cost f g hf hg, st_costStar f g hf hg, ← sub_nonneg]
  have hI : ∫ x, (cntW f g A B ψ x - cntW f g A B φ x - stW f g A B φ ψ x) =
      (∫ x, cntW f g A B ψ x) - ((∫ x, cntW f g A B φ x) + ∫ x, stW f g A B φ ψ x) := by
    have i1 : Integrable (fun x => cntW f g A B ψ x - cntW f g A B φ x) :=
      (cnt_W_int f g hf hg A B ψ).sub (cnt_W_int f g hf hg A B φ)
    rw [integral_sub i1 (st_W_int f g hf hg A B φ ψ), integral_sub (cnt_W_int f g hf hg A B ψ)
      (cnt_W_int f g hf hg A B φ)]
    ring
  rw [← hI]
  have hfin : (Set.range A ∪ Set.range B).Finite :=
    (Set.finite_range A).union (Set.finite_range B)
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ Set.range A ∪ Set.range B :=
    measure_eq_zero_iff_ae_notMem.mp (hfin.measure_zero _)
  apply integral_nonneg_of_ae
  filter_upwards [hae] with x hx
  have hxA : ∀ i, x ≠ A i := fun i h => hx (Or.inl ⟨i, h.symm⟩)
  have hxB : ∀ i, x ≠ B i := fun i h => hx (Or.inr ⟨i, h.symm⟩)
  show 0 ≤ cntW f g A B ψ x - cntW f g A B φ x - stW f g A B φ ψ x
  by_cases hP : x ∈ P A B φ
  · rw [st_in f g A B φ ψ x hP hxA hxB, st_phi_zero f g A B hB φ hφ x hP hxA hxB]
    simp
  · rw [st_out f g A B φ ψ x hP, sub_zero, cnt_W_sub]
    exact mul_nonneg (sub_nonneg.mpr (cnt_Ng_le A B hB φ hφ ψ x)) (hfg x)

lemma l7_adj (φ ψ : Equiv.Perm (Fin (n + 1))) (q : Fin n) (hq : q ∈ starArcs φ ψ) :
    (graphStar φ ψ).Adj q.castSucc q.succ := by
  have hne : q.castSucc ≠ q.succ := (Fin.castSucc_lt_succ).ne
  refine (SimpleGraph.sup_adj _ _ _ _).mpr (Or.inr ?_)
  simp only [SimpleGraph.fromRel_adj]
  refine ⟨hne, Or.inl ?_⟩
  simp only [adjArcs, Finset.mem_image]
  exact ⟨q, hq, rfl⟩

lemma l7_interval (φ ψ : Equiv.Perm (Fin (n + 1))) :
    ∀ (k : ℕ) (a b : Fin (n + 1)), b.val = a.val + k →
      (∀ q : Fin n, a ≤ q.castSucc → q.castSucc < b → q ∈ starArcs φ ψ) →
      (graphStar φ ψ).Reachable a b := by
  intro k
  induction k with
  | zero =>
    intro a b hab _
    have : a = b := Fin.ext (by omega)
    subst this; exact SimpleGraph.Reachable.refl _
  | succ k ih =>
    intro a b hab hq
    have han : a.val < n := by have := b.isLt; omega
    let c : Fin n := ⟨a.val, han⟩
    have hc1 : c.castSucc = a := Fin.ext rfl
    have hc2 : c.succ.val = a.val + 1 := rfl
    have h1 : (graphStar φ ψ).Reachable a c.succ := by
      have := l7_adj φ ψ c (hq c (by rw [hc1]) (by
        rw [Fin.lt_def]; show a.val < b.val; omega))
      rw [hc1] at this
      exact this.reachable
    refine h1.trans (ih c.succ b (by omega) ?_)
    intro q h1q h2q
    have h3 : c.succ.val ≤ q.castSucc.val := h1q
    have h4 : a.val ≤ q.castSucc.val := by omega
    exact hq q h4 h2q

lemma l7_core (φ ψ : Equiv.Perm (Fin (n + 1))) (hψ : IsTour ψ) :
    (graphStar φ ψ).Connected := by
  classical
  have hstep : ∀ x : Fin (n+1), (graphStar φ ψ).Reachable x (φ.symm (ψ x)) := by
    intro x
    rcases le_total x (φ.symm (ψ x)) with h | h
    · refine l7_interval φ ψ ((φ.symm (ψ x)).val - x.val) x _ (by
        have := Fin.le_def.mp h; omega) ?_
      intro q h1 h2
      simp only [starArcs, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Or.inl ⟨x, h1, h2⟩
    · refine (l7_interval φ ψ (x.val - (φ.symm (ψ x)).val) (φ.symm (ψ x)) x (by
        have := Fin.le_def.mp h; omega) ?_).symm
      intro q h1 h2
      simp only [starArcs, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Or.inr ⟨x, h1, h2⟩
  have hφ : ∀ x : Fin (n+1), (graphStar φ ψ).Reachable x (φ x) := by
    intro x
    by_cases h : φ x = x
    · rw [h]
    · apply SimpleGraph.Adj.reachable
      refine (SimpleGraph.sup_adj _ _ _ _).mpr (Or.inl ?_)
      simp only [graph, SimpleGraph.fromRel_adj]
      exact ⟨fun h' => h h'.symm, by simp⟩
  have hψx : ∀ x : Fin (n+1), (graphStar φ ψ).Reachable x (ψ x) := by
    intro x
    have h1 := hstep x
    have h2 := hφ (φ.symm (ψ x))
    simp only [Equiv.apply_symm_apply] at h2
    exact h1.trans h2
  let x0 : Fin (n+1) := 0
  let s : Finset (Fin (n+1)) := Finset.univ.filter fun y => (graphStar φ ψ).Reachable x0 y
  have hsub : s.map ψ.toEmbedding ⊆ s := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hz
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact hy.trans (hψx y)
  have heq : s.map ψ.toEmbedding = s :=
    Finset.eq_of_subset_of_card_le hsub (by simp)
  have hall : s = Finset.univ := by
    by_contra hne
    exact hψ s ⟨x0, by simp [s]⟩ hne heq
  have hreach : ∀ y, (graphStar φ ψ).Reachable x0 y := by
    intro y
    have : y ∈ s := by rw [hall]; exact Finset.mem_univ _
    simpa [s] using this
  refine ⟨fun u v => ?_⟩
  exact (hreach u).symm.trans (hreach v)

lemma e28_nonneg (f g : ℝ → ℝ) (hf : LocallyIntegrable f) (hg : LocallyIntegrable g)
    (hfg : ∀ x, 0 ≤ f x + g x) (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : RanksA A φ) (q : Fin n) :
    interchangeCost f g A B φ q.castSucc q.succ = ∫ x in Pq A B φ q, (f x + g x) := by
  exact eq_11_core f g hf hg hfg A B φ _ _ (hB (Fin.castSucc_lt_succ).le)
    (hφ (Fin.castSucc_lt_succ).le)

lemma e28_pq_meas (A B : Fin (n + 1) → ℝ) (φ : Equiv.Perm (Fin (n + 1))) (q : Fin n) :
    MeasurableSet (Pq A B φ q) := measurableSet_Icc.inter measurableSet_Icc

lemma e28_tree_sub (φ : Equiv.Perm (Fin (n + 1))) (S : Finset (Fin n))
    (hS : (graphWith φ (adjArcs S)).Connected) : ∃ T' ⊆ S, IsAdjTree φ T' := by
  classical
  have hne : ((S.powerset).filter fun S' => (graphWith φ (adjArcs S')).Connected).Nonempty :=
    ⟨S, by simp [hS]⟩
  obtain ⟨S', hS'mem, hmin⟩ := Finset.exists_min_image _ Finset.card hne
  simp only [Finset.mem_filter, Finset.mem_powerset] at hS'mem
  refine ⟨S', hS'mem.1, hS'mem.2, ?_⟩
  intro E' hE' hconn
  set S'' := S'.filter (fun q => adjArc q ∈ E') with hS''
  have hadj : adjArcs S'' = E' := by
    ext e
    simp only [adjArcs, Finset.mem_image, hS'', Finset.mem_filter]
    constructor
    · rintro ⟨q, ⟨_, hq⟩, rfl⟩; exact hq
    · intro he
      have : e ∈ adjArcs S' := hE'.subset he
      simp only [adjArcs, Finset.mem_image] at this
      obtain ⟨q, hq, rfl⟩ := this
      exact ⟨q, ⟨hq, he⟩, rfl⟩
  have hss : S'' ⊂ S' := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, fun h => ?_⟩
    rw [h] at hadj
    rw [hadj] at hE'
    exact lt_irrefl _ hE'
  have := hmin S'' (by
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨(Finset.filter_subset _ _).trans hS'mem.1, by rw [hadj]; exact hconn⟩)
  exact absurd (Finset.card_lt_card hss) (not_lt.mpr this)

theorem eq_28_core {n : ℕ}
    (f g : ℝ → ℝ) (hf : MeasureTheory.LocallyIntegrable f) (hg : MeasureTheory.LocallyIntegrable g)
    (hfg : ∀ x, 0 ≤ f x + g x) (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : RanksA A φ)
    (ψ : Equiv.Perm (Fin (n + 1))) (hψ : IsTour ψ)
    (T : Finset (Fin n)) (hT : IsMinCostAdjTree f g A B φ T) :
    adjTreeCost f g A B φ T ≤ costStar f g A B φ ψ := by
  classical
  set S := starArcs φ ψ with hSdef
  -- the tree inside the star arcs
  obtain ⟨T', hT'S, hT'⟩ := e28_tree_sub φ S (l7_core φ ψ hψ)
  have hnn : ∀ q : Fin n, 0 ≤ interchangeCost f g A B φ q.castSucc q.succ := by
    intro q
    rw [e28_nonneg f g hf hg hfg A B hB φ hφ q]
    exact integral_nonneg (fun x => hfg x)
  have h1 : adjTreeCost f g A B φ T ≤ adjTreeCost f g A B φ T' := hT.2 T' hT'
  have h2 : adjTreeCost f g A B φ T' ≤ adjTreeCost f g A B φ S :=
    Finset.sum_le_sum_of_subset_of_nonneg hT'S (fun q _ _ => hnn q)
  refine h1.trans (h2.trans ?_)
  -- integral comparison
  let Φ : ℝ → ℝ := fun x => ∑ q ∈ S, (Pq A B φ q).indicator (fun x => f x + g x) x
  have hIq : ∀ q : Fin n, Integrable ((Pq A B φ q).indicator (fun x => f x + g x)) := by
    intro q
    exact (integrable_indicator_iff (e28_pq_meas A B φ q)).mpr
      (((hf.add hg).integrableOn_isCompact isCompact_Icc).mono_set
        (Set.inter_subset_left))
  have hΦint : Integrable Φ := integrable_finsetSum _ (fun q _ => hIq q)
  have hΦ : ∫ x, Φ x = adjTreeCost f g A B φ S := by
    simp only [Φ]
    rw [integral_finsetSum _ (fun q _ => hIq q)]
    unfold adjTreeCost
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [integral_indicator (e28_pq_meas A B φ q), e28_nonneg f g hf hg hfg A B hB φ hφ q]
  rw [← hΦ, st_costStar f g hf hg]
  have hfin : (Set.range A ∪ Set.range B).Finite :=
    (Set.finite_range A).union (Set.finite_range B)
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ Set.range A ∪ Set.range B :=
    measure_eq_zero_iff_ae_notMem.mp (hfin.measure_zero _)
  refine integral_mono_ae hΦint (st_W_int f g hf hg A B φ ψ) ?_
  filter_upwards [hae] with x hx
  have hxA : ∀ i, x ≠ A i := fun i h => hx (Or.inl ⟨i, h.symm⟩)
  have hxB : ∀ i, x ≠ B i := fun i h => hx (Or.inr ⟨i, h.symm⟩)
  show Φ x ≤ stW f g A B φ ψ x
  by_cases hP : x ∈ P A B φ
  · obtain ⟨q0, hq0⟩ := Set.mem_iUnion.mp hP
    have hq0' := hq0
    simp only [Pq, Set.mem_inter_iff, Set.mem_Icc] at hq0'
    obtain ⟨⟨hb1, hb2⟩, ha1, ha2⟩ := hq0'
    -- index characterizations
    have hBiff : ∀ i, B i ≤ x ↔ i ≤ q0.castSucc := by
      intro i
      constructor
      · intro h
        by_contra hc
        push Not at hc
        have : q0.succ ≤ i := Fin.castSucc_lt_iff_succ_le.mp hc
        have := hB this
        exact hxB _ (le_antisymm hb2 (by linarith))
      · intro h; exact (hB h).trans hb1
    have hAiff : ∀ i, A (φ i) ≤ x ↔ i ≤ q0.castSucc := by
      intro i
      constructor
      · intro h
        by_contra hc
        push Not at hc
        have h' : q0.succ ≤ i := Fin.castSucc_lt_iff_succ_le.mp hc
        have := hφ h'
        simp only [Function.comp] at this
        exact hxA _ (le_antisymm ha2 (by linarith))
      · intro h
        have := hφ h
        simp only [Function.comp] at this
        linarith
    have hD : cntD A B x = 0 := by
      unfold cntD
      have : ∑ i, (if A i ≤ x then (1:ℝ) else 0) = ∑ i, if A (φ i) ≤ x then (1:ℝ) else 0 :=
        (Equiv.sum_comp φ (fun j => if A j ≤ x then (1:ℝ) else 0)).symm
      rw [this, sub_eq_zero]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [hBiff, hAiff]
    have hNeq : cntNf A B ψ x = cntNg A B ψ x := by
      have := cnt_diff A B ψ x; linarith
    have hst : stW f g A B φ ψ x = cntNf A B ψ x * (f x + g x) := by
      rw [st_in f g A B φ ψ x hP hxA hxB, cnt_W_eq, ← hNeq]; ring
    -- uniqueness of the interval
    have huniq : ∀ q : Fin n, x ∈ Pq A B φ q → q = q0 := by
      intro q hq
      have hq' := hq
      simp only [Pq, Set.mem_inter_iff, Set.mem_Icc] at hq'
      obtain ⟨⟨c1, c2⟩, _, _⟩ := hq'
      have e1 : q.castSucc ≤ q0.castSucc := (hBiff _).mp c1
      have e2 : q0.castSucc ≤ q.castSucc := by
        by_contra hc
        push Not at hc
        have h' : q.succ ≤ q0.castSucc := Fin.castSucc_lt_iff_succ_le.mp hc
        have := hB h'
        exact hxB _ (le_antisymm c2 (by linarith [(hBiff q0.castSucc).mpr le_rfl]))
      exact Fin.castSucc_injective _ (le_antisymm e1 e2)
    have hNf1 : q0 ∈ S → 1 ≤ cntNf A B ψ x := by
      intro hq0S
      simp only [hSdef, starArcs, Finset.mem_filter, Finset.mem_univ, true_and] at hq0S
      rcases hq0S with ⟨i, hi1, hi2⟩ | ⟨j, hj1, hj2⟩
      · have hBi : B i ≤ x := (hBiff i).mpr hi1
        have hAi : x < A (ψ i) := by
          have h3 : ¬ A (φ (φ.symm (ψ i))) ≤ x := by
            rw [hAiff]; exact not_le.mpr hi2
          rw [Equiv.apply_symm_apply] at h3
          exact not_le.mp h3
        have hterm : (if B i ≤ x ∧ x < A (ψ i) then (1:ℝ) else 0) = 1 := if_pos ⟨hBi, hAi⟩
        have := Finset.single_le_sum (f := fun i => if B i ≤ x ∧ x < A (ψ i) then (1:ℝ) else 0)
          (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
        unfold cntNf
        simp only [hterm] at this
        exact this
      · have hAj : A (ψ j) ≤ x := by
          have h3 := (hAiff (φ.symm (ψ j))).mpr hj1
          rwa [Equiv.apply_symm_apply] at h3
        have hBj : x < B j := by
          have h3 : ¬ B j ≤ x := by rw [hBiff]; exact not_le.mpr hj2
          exact not_le.mp h3
        have hterm : (if A (ψ j) ≤ x ∧ x < B j then (1:ℝ) else 0) = 1 := if_pos ⟨hAj, hBj⟩
        have := Finset.single_le_sum (f := fun i => if A (ψ i) ≤ x ∧ x < B i then (1:ℝ) else 0)
          (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ j)
        simp only [hterm] at this
        rw [hNeq]
        unfold cntNg
        exact this
    by_cases hq0S : q0 ∈ S
    · have hΦx : Φ x = f x + g x := by
        simp only [Φ]
        rw [Finset.sum_eq_single q0]
        · exact Set.indicator_of_mem hq0 _
        · intro q _ hq
          exact Set.indicator_of_notMem (fun h => hq (huniq q h)) _
        · intro h; exact absurd hq0S h
      rw [hΦx, hst]
      exact le_mul_of_one_le_left (hfg x) (hNf1 hq0S)
    · have hΦx : Φ x = 0 := by
        refine Finset.sum_eq_zero (fun q hq => ?_)
        have hqq : q ≠ q0 := fun h => hq0S (h ▸ hq)
        exact Set.indicator_of_notMem (fun h => hqq (huniq q h)) _
      rw [hΦx, hst]
      exact mul_nonneg (cntNf_nonneg A B ψ x) (hfg x)
  · have : Φ x = 0 := by
      simp only [Φ]
      refine Finset.sum_eq_zero (fun q _ => ?_)
      exact Set.indicator_of_notMem (fun h => hP (Set.mem_iUnion.mpr ⟨q, h⟩)) _
    rw [this, st_out f g A B φ ψ x hP]



lemma l2_adj (φ : Equiv.Perm (Fin (n + 1))) (S : Finset (Fin n)) (q : Fin n) (hq : q ∈ S) :
    (graphWith φ (adjArcs S)).Adj q.castSucc q.succ := by
  have hne : q.castSucc ≠ q.succ := (Fin.castSucc_lt_succ).ne
  refine t2_gadj_edge φ _ hne ?_
  simp only [adjArcs, Finset.mem_image]
  exact ⟨q, hq, rfl⟩

lemma l2_interval (φ : Equiv.Perm (Fin (n + 1))) (S : Finset (Fin n)) :
    ∀ (k : ℕ) (a b : Fin (n + 1)), b.val = a.val + k →
      (∀ q : Fin n, a ≤ q.castSucc → q.castSucc < b → q ∈ S) →
      (graphWith φ (adjArcs S)).Reachable a b := by
  intro k
  induction k with
  | zero =>
    intro a b hab _
    have : a = b := Fin.ext (by omega)
    subst this; exact SimpleGraph.Reachable.refl _
  | succ k ih =>
    intro a b hab hq
    have han : a.val < n := by have := b.isLt; omega
    let c : Fin n := ⟨a.val, han⟩
    have hc1 : c.castSucc = a := Fin.ext rfl
    have hc2 : c.succ.val = a.val + 1 := rfl
    have h1 : (graphWith φ (adjArcs S)).Reachable a c.succ := by
      have := l2_adj φ S c (hq c (by rw [hc1]) (by
        rw [Fin.lt_def]; show a.val < b.val; omega))
      rw [hc1] at this
      exact this.reachable
    refine h1.trans (ih c.succ b (by omega) ?_)
    intro q h1q h2q
    have h3 : c.succ.val ≤ q.castSucc.val := h1q
    have h4 : a.val ≤ q.castSucc.val := by omega
    exact hq q h4 h2q

def L2Q (i j : Fin (n + 1)) : Finset (Fin n) :=
  Finset.univ.filter fun q => min i j ≤ q.castSucc ∧ q.succ ≤ max i j

lemma l2_sumPq (h : ℝ → ℝ) (hh : LocallyIntegrable h) (hnn : ∀ x, 0 ≤ h x)
    (A B : Fin (n + 1) → ℝ) (hB : Monotone B) (φ : Equiv.Perm (Fin (n + 1)))
    (Q : Finset (Fin n)) (u v u' v' : ℝ)
    (hQZ : ∀ q ∈ Q, Pq A B φ q ⊆ Set.Icc u v ∩ Set.Icc u' v') :
    ∑ q ∈ Q, ∫ x in Pq A B φ q, h x ≤ ∫ x in Set.Icc u v ∩ Set.Icc u' v', h x := by
  have hZ : MeasurableSet (Set.Icc u v ∩ Set.Icc u' v') := measurableSet_Icc.inter measurableSet_Icc
  have hIq : ∀ q : Fin n, Integrable ((Pq A B φ q).indicator h) := by
    intro q
    exact (integrable_indicator_iff (e28_pq_meas A B φ q)).mpr
      ((hh.integrableOn_isCompact isCompact_Icc).mono_set Set.inter_subset_left)
  have hIZ : Integrable ((Set.Icc u v ∩ Set.Icc u' v').indicator h) :=
    (integrable_indicator_iff hZ).mpr
      ((hh.integrableOn_isCompact isCompact_Icc).mono_set Set.inter_subset_left)
  have e1 : ∑ q ∈ Q, ∫ x in Pq A B φ q, h x = ∫ x, ∑ q ∈ Q, (Pq A B φ q).indicator h x := by
    rw [integral_finsetSum _ (fun q _ => hIq q)]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [integral_indicator (e28_pq_meas A B φ q)]
  rw [e1, ← integral_indicator hZ]
  have hfin : (Set.range B).Finite := Set.finite_range B
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ Set.range B :=
    measure_eq_zero_iff_ae_notMem.mp (hfin.measure_zero _)
  refine integral_mono_ae (integrable_finsetSum _ (fun q _ => hIq q)) hIZ ?_
  filter_upwards [hae] with x hx
  have hxB : ∀ i, x ≠ B i := fun i hi => hx ⟨i, hi.symm⟩
  have huniq : ∀ q q' : Fin n, x ∈ Pq A B φ q → x ∈ Pq A B φ q' → q = q' := by
    have key : ∀ q q' : Fin n, x ∈ Pq A B φ q → x ∈ Pq A B φ q' → ¬ q < q' := by
      intro q q' hq hq' hlt
      simp only [Pq, Set.mem_inter_iff, Set.mem_Icc] at hq hq'
      have h' : q.succ ≤ q'.castSucc := Fin.castSucc_lt_iff_succ_le.mp ?_
      · have := hB h'
        exact hxB _ (le_antisymm hq.1.2 (by linarith [hq'.1.1]))
      · exact (Fin.castSucc_lt_castSucc_iff.mpr hlt) |> fun h => by simpa using h
    intro q q' hq hq'
    rcases lt_trichotomy q q' with h | h | h
    · exact absurd h (key q q' hq hq')
    · exact h
    · exact absurd h (key q' q hq' hq)
  by_cases hex : ∃ q ∈ Q, x ∈ Pq A B φ q
  · obtain ⟨q0, hq0, hx0⟩ := hex
    rw [Finset.sum_eq_single_of_mem q0 hq0 (fun q _ hne => Set.indicator_of_notMem
      (fun hh' => hne (huniq q q0 hh' hx0)) _)]
    rw [Set.indicator_of_mem hx0, Set.indicator_of_mem (hQZ q0 hq0 hx0)]
  · push Not at hex
    rw [Finset.sum_eq_zero (fun q hq => Set.indicator_of_notMem (hex q hq) _)]
    exact Set.indicator_nonneg (fun y _ => hnn y) x

lemma l2_arc (f g : ℝ → ℝ) (hf : LocallyIntegrable f) (hg : LocallyIntegrable g)
    (hfg : ∀ x, 0 ≤ f x + g x) (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : RanksA A φ) (i j : Fin (n + 1)) :
    ∑ q ∈ L2Q i j, interchangeCost f g A B φ q.castSucc q.succ ≤ interchangeCost f g A B φ i j := by
  have key : ∀ i j : Fin (n + 1), i ≤ j →
      ∑ q ∈ L2Q i j, interchangeCost f g A B φ q.castSucc q.succ ≤
        interchangeCost f g A B φ i j := by
    intro i j hij
    rw [eq_11_core f g hf hg hfg A B φ i j (hB hij) (hφ hij)]
    have hsum : ∑ q ∈ L2Q i j, interchangeCost f g A B φ q.castSucc q.succ =
        ∑ q ∈ L2Q i j, ∫ x in Pq A B φ q, (f x + g x) :=
      Finset.sum_congr rfl (fun q _ => e28_nonneg f g hf hg hfg A B hB φ hφ q)
    rw [hsum]
    refine l2_sumPq (fun x => f x + g x) (hf.add hg) hfg A B hB φ _ _ _ _ _ ?_
    intro q hq x hx
    simp only [L2Q, Finset.mem_filter, Finset.mem_univ, true_and, min_eq_left hij,
      max_eq_right hij] at hq
    simp only [Pq, Set.mem_inter_iff, Set.mem_Icc] at hx ⊢
    have h1 := hB hq.1
    have h2 := hB hq.2
    have h3 := hφ hq.1
    have h4 := hφ hq.2
    simp only [Function.comp] at h3 h4
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [hx.1.1, hx.1.2, hx.2.1, hx.2.2]
  rcases le_total i j with h | h
  · exact key i j h
  · have e : interchangeCost f g A B φ i j = interchangeCost f g A B φ j i := by
      unfold interchangeCost alpha
      rw [Equiv.swap_comm]
    have eQ : L2Q i j = L2Q j i := by
      unfold L2Q; rw [min_comm, max_comm]
    rw [e, eQ]
    exact key j i h

lemma l2_biUnion_le (c : Fin n → ℝ) (hc : ∀ q, 0 ≤ c q)
    {ι : Type*} [DecidableEq ι] (E : Finset ι) (Q : ι → Finset (Fin n)) :
    ∑ q ∈ E.biUnion Q, c q ≤ ∑ e ∈ E, ∑ q ∈ Q e, c q := by
  classical
  induction E using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have := Finset.sum_union_inter (s₁ := Q a) (s₂ := s.biUnion Q) (f := c)
    have h0 : 0 ≤ ∑ q ∈ Q a ∩ s.biUnion Q, c q := Finset.sum_nonneg (fun q _ => hc q)
    linarith

theorem lemma_2_core {n : ℕ}
    (f g : ℝ → ℝ) (hf : MeasureTheory.LocallyIntegrable f) (hg : MeasureTheory.LocallyIntegrable g)
    (hfg : ∀ x, 0 ≤ f x + g x) (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : RanksA A φ) :
    ∃ T : Finset (Fin n), IsAdjTree φ T ∧
      ∀ E : Finset (Fin (n + 1) × Fin (n + 1)), IsSpanningTree φ E →
        adjTreeCost f g A B φ T ≤ arcSetCost f g A B φ E := by
  classical
  have hnn : ∀ q : Fin n, 0 ≤ interchangeCost f g A B φ q.castSucc q.succ := by
    intro q
    rw [e28_nonneg f g hf hg hfg A B hB φ hφ q]
    exact integral_nonneg (fun x => hfg x)
  have hconn_univ : (graphWith φ (adjArcs (Finset.univ : Finset (Fin n)))).Connected := by
    have hr : ∀ x : Fin (n + 1), (graphWith φ (adjArcs (Finset.univ : Finset (Fin n)))).Reachable 0 x := by
      intro x
      exact l2_interval φ Finset.univ (x.val - 0) 0 x (by simp) (fun q _ _ => Finset.mem_univ q)
    refine ⟨fun u v => ?_⟩
    exact (hr u).symm.trans (hr v)
  obtain ⟨T1, _, hT1⟩ := e28_tree_sub φ Finset.univ hconn_univ
  let 𝒯 : Finset (Finset (Fin n)) := (Finset.univ : Finset (Finset (Fin n))).filter
    (fun T => IsAdjTree φ T)
  obtain ⟨T0, hT0mem, hT0min⟩ := Finset.exists_min_image 𝒯 (adjTreeCost f g A B φ)
    ⟨T1, by simp [𝒯, hT1]⟩
  have hT0 : IsAdjTree φ T0 := by simpa [𝒯] using hT0mem
  refine ⟨T0, hT0, fun E hE => ?_⟩
  set S : Finset (Fin n) := E.biUnion (fun e => L2Q e.1 e.2) with hS
  have hSconn : (graphWith φ (adjArcs S)).Connected := by
    refine t2_conn ?_ hE.1
    intro a b hab
    rcases t2_gadj_cases φ E hab with h | ⟨hne, h | h⟩
    · exact (t2_gadj_graph φ _ h).reachable
    · rcases lt_or_gt_of_ne hne with hlt | hlt
      · refine l2_interval φ S (b.val - a.val) a b (by have := Fin.lt_def.mp hlt; omega) ?_
        intro q h1 h2
        rw [hS, Finset.mem_biUnion]
        refine ⟨(a, b), h, ?_⟩
        simp only [L2Q, Finset.mem_filter, Finset.mem_univ, true_and, min_eq_left hlt.le,
          max_eq_right hlt.le]
        exact ⟨h1, Fin.castSucc_lt_iff_succ_le.mp h2⟩
      · refine (l2_interval φ S (a.val - b.val) b a (by have := Fin.lt_def.mp hlt; omega) ?_).symm
        intro q h1 h2
        rw [hS, Finset.mem_biUnion]
        refine ⟨(a, b), h, ?_⟩
        simp only [L2Q, Finset.mem_filter, Finset.mem_univ, true_and, min_eq_right hlt.le,
          max_eq_left hlt.le]
        exact ⟨h1, Fin.castSucc_lt_iff_succ_le.mp h2⟩
    · rcases lt_or_gt_of_ne hne with hlt | hlt
      · refine l2_interval φ S (b.val - a.val) a b (by have := Fin.lt_def.mp hlt; omega) ?_
        intro q h1 h2
        rw [hS, Finset.mem_biUnion]
        refine ⟨(b, a), h, ?_⟩
        simp only [L2Q, Finset.mem_filter, Finset.mem_univ, true_and, min_eq_right hlt.le,
          max_eq_left hlt.le]
        exact ⟨h1, Fin.castSucc_lt_iff_succ_le.mp h2⟩
      · refine (l2_interval φ S (a.val - b.val) b a (by have := Fin.lt_def.mp hlt; omega) ?_).symm
        intro q h1 h2
        rw [hS, Finset.mem_biUnion]
        refine ⟨(b, a), h, ?_⟩
        simp only [L2Q, Finset.mem_filter, Finset.mem_univ, true_and, min_eq_left hlt.le,
          max_eq_right hlt.le]
        exact ⟨h1, Fin.castSucc_lt_iff_succ_le.mp h2⟩
  obtain ⟨T', hT'S, hT'⟩ := e28_tree_sub φ S hSconn
  calc adjTreeCost f g A B φ T0 ≤ adjTreeCost f g A B φ T' :=
        hT0min T' (by simpa [𝒯] using hT')
    _ ≤ adjTreeCost f g A B φ S :=
        Finset.sum_le_sum_of_subset_of_nonneg hT'S (fun q _ _ => hnn q)
    _ ≤ ∑ e ∈ E, ∑ q ∈ L2Q e.1 e.2, interchangeCost f g A B φ q.castSucc q.succ :=
        l2_biUnion_le _ hnn E _
    _ ≤ arcSetCost f g A B φ E :=
        Finset.sum_le_sum (fun e _ => l2_arc f g hf hg hfg A B hB φ hφ e.1 e.2)

end GilmoreGomoryTSP.MinCost

open GilmoreGomoryTSP.MinCost


theorem solution {n : ℕ}
    (f g : ℝ → ℝ) (hf : MeasureTheory.LocallyIntegrable f) (hg : MeasureTheory.LocallyIntegrable g)
    (hfg : ∀ x, 0 ≤ f x + g x) (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : RanksA A φ) :
    ∃ T : Finset (Fin n), IsAdjTree φ T ∧
      ∀ E : Finset (Fin (n + 1) × Fin (n + 1)), IsSpanningTree φ E →
        adjTreeCost f g A B φ T ≤ arcSetCost f g A B φ E := by
  exact lemma_2_core f g hf hg hfg A B hB φ hφ
