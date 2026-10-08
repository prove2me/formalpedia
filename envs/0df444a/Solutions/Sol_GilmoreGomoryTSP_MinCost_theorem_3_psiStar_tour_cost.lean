-- Prove2me | solution 1 for GilmoreGomoryTSP.MinCost.theorem_3_psiStar_tour_cost
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:54:33.866451+00:00
-- url     : https://prove2.me/submissions/9e228c5a-6e87-419c-ac57-5c62f82fba99

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

end GilmoreGomoryTSP.MinCost

open GilmoreGomoryTSP.MinCost


theorem solution {n : ℕ}
    (f g : ℝ → ℝ) (hf : MeasureTheory.LocallyIntegrable f) (hg : MeasureTheory.LocallyIntegrable g)
    (hfg : ∀ x, 0 ≤ f x + g x) (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : RanksA A φ)
    (T : Finset (Fin n)) (hT : IsMinCostAdjTree f g A B φ T) :
    IsTour (psiStar A B φ T) ∧
      cost f g A B (psiStar A B φ T) = cost f g A B φ + adjTreeCost f g A B φ T := by
  exact theorem_3_core f g hf hg hfg A B hB φ hφ T hT
