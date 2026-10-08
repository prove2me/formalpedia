-- Prove2me | solution 1 for KVVMatching.Ranking.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T18:27:43.208196+00:00
-- url     : https://prove2.me/submissions/0cd92a8d-919e-42a7-aa7a-7d7d16c728b9

import Mathlib
import Definitions.Def_KVVMatching_Ranking_Algorithms
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsPerfectMatchingBij



namespace KVVMatching.Ranking

open Classical in
/-- one step of greedyRun -/
noncomputable def gstep {n : ℕ} (adj : Fin n → Fin n → Prop)
    (arrivals rank : Equiv.Perm (Fin n))
    (refuse : ℕ → Finset (Fin n × Fin n) → Fin n → Bool)
    (M : Finset (Fin n × Fin n)) (t : ℕ) : Finset (Fin n × Fin n) :=
    if ht : t < n then
      let a : Fin n := ⟨t, ht⟩
      let v := arrivals a
      if refuse t M v then M else
        let eligible : Finset (Fin n) := Finset.univ.filter
          (fun r => adj v (rank r) ∧ ¬ secondMatched M (rank r))
        if he : eligible.Nonempty then
          insert (v, rank (eligible.min' he)) M
        else M
    else M

theorem greedyRun_eq {n : ℕ} (adj : Fin n → Fin n → Prop)
    (arrivals rank : Equiv.Perm (Fin n))
    (refuse : ℕ → Finset (Fin n × Fin n) → Fin n → Bool) :
    greedyRun adj arrivals rank refuse =
      (List.range n).foldl (gstep adj arrivals rank refuse) ∅ := rfl

noncomputable def GG {n : ℕ} (adj : Fin n → Fin n → Prop)
    (arrivals rank : Equiv.Perm (Fin n))
    (refuse : ℕ → Finset (Fin n × Fin n) → Fin n → Bool) (k : ℕ) :
    Finset (Fin n × Fin n) :=
  (List.range k).foldl (gstep adj arrivals rank refuse) ∅

theorem GG_succ {n : ℕ} (adj : Fin n → Fin n → Prop)
    (arrivals rank : Equiv.Perm (Fin n))
    (refuse : ℕ → Finset (Fin n × Fin n) → Fin n → Bool) (k : ℕ) :
    GG adj arrivals rank refuse (k+1) =
      gstep adj arrivals rank refuse (GG adj arrivals rank refuse k) k := by
  unfold GG
  rw [List.range_succ, List.foldl_append]
  rfl

theorem greedyRun_GG {n : ℕ} (adj : Fin n → Fin n → Prop)
    (arrivals rank : Equiv.Perm (Fin n))
    (refuse : ℕ → Finset (Fin n × Fin n) → Fin n → Bool) :
    greedyRun adj arrivals rank refuse = GG adj arrivals rank refuse n := rfl

/-- structure of a step -/
theorem gstep_cases {n : ℕ} (adj : Fin n → Fin n → Prop)
    (arrivals rank : Equiv.Perm (Fin n))
    (refuse : ℕ → Finset (Fin n × Fin n) → Fin n → Bool)
    (M : Finset (Fin n × Fin n)) (t : ℕ) (ht : t < n) :
    gstep adj arrivals rank refuse M t = M ∨
    ∃ r : Fin n, adj (arrivals ⟨t, ht⟩) (rank r) ∧ ¬ secondMatched M (rank r) ∧
      (∀ r' : Fin n, adj (arrivals ⟨t, ht⟩) (rank r') ∧ ¬ secondMatched M (rank r') → r ≤ r') ∧
      gstep adj arrivals rank refuse M t = insert (arrivals ⟨t, ht⟩, rank r) M := by
  classical
  unfold gstep
  simp only [ht, dif_pos]
  by_cases hr : refuse t M (arrivals ⟨t, ht⟩) = true
  · left; simp [hr]
  · simp only [hr, if_false]
    by_cases he : (Finset.univ.filter
          (fun r => adj (arrivals ⟨t, ht⟩) (rank r) ∧ ¬ secondMatched M (rank r))).Nonempty
    · right
      rw [dif_pos he]
      refine ⟨_, ?_, ?_, ?_, rfl⟩
      · have := Finset.min'_mem _ he
        simp only [Finset.mem_filter] at this
        exact this.2.1
      · have := Finset.min'_mem _ he
        simp only [Finset.mem_filter] at this
        exact this.2.2
      · intro r' hr'
        apply Finset.min'_le
        simp [hr']
    · left; rw [dif_neg he]; simp

theorem gstep_elig {n : ℕ} (adj : Fin n → Fin n → Prop)
    (arrivals rank : Equiv.Perm (Fin n))
    (M : Finset (Fin n × Fin n)) (t : ℕ) (ht : t < n)
    (h0 : ∃ r0 : Fin n, adj (arrivals ⟨t, ht⟩) (rank r0) ∧ ¬ secondMatched M (rank r0)) :
    ∃ r : Fin n, adj (arrivals ⟨t, ht⟩) (rank r) ∧ ¬ secondMatched M (rank r) ∧
      (∀ r' : Fin n, adj (arrivals ⟨t, ht⟩) (rank r') ∧ ¬ secondMatched M (rank r') → r ≤ r') ∧
      gstep adj arrivals rank (fun _ _ _ => false) M t = insert (arrivals ⟨t, ht⟩, rank r) M := by
  classical
  rcases gstep_cases adj arrivals rank (fun _ _ _ => false) M t ht with h | h
  · exfalso
    obtain ⟨r0, h1, h2⟩ := h0
    unfold gstep at h
    simp only [ht, dif_pos] at h
    have he : (Finset.univ.filter
          (fun r => adj (arrivals ⟨t, ht⟩) (rank r) ∧ ¬ secondMatched M (rank r))).Nonempty :=
      ⟨r0, by simp [h1, h2]⟩
    rw [dif_pos he] at h
    simp only [Bool.false_eq_true, if_false] at h
    have hmem := Finset.insert_eq_self.mp h
    have := Finset.min'_mem _ he
    simp only [Finset.mem_filter] at this
    exact this.2.2 ⟨_, hmem, rfl⟩
  · exact h

theorem gstep_sub {n : ℕ} (adj : Fin n → Fin n → Prop)
    (arrivals rank : Equiv.Perm (Fin n))
    (refuse : ℕ → Finset (Fin n × Fin n) → Fin n → Bool)
    (M : Finset (Fin n × Fin n)) (t : ℕ) :
    M ⊆ gstep adj arrivals rank refuse M t := by
  by_cases ht : t < n
  · rcases gstep_cases adj arrivals rank refuse M t ht with h | ⟨r, _, _, _, h⟩
    · rw [h]
    · rw [h]; exact Finset.subset_insert _ _
  · unfold gstep; simp [ht]

theorem GG_mono {n : ℕ} (adj : Fin n → Fin n → Prop)
    (arrivals rank : Equiv.Perm (Fin n))
    (refuse : ℕ → Finset (Fin n × Fin n) → Fin n → Bool) {k m : ℕ} (h : k ≤ m) :
    GG adj arrivals rank refuse k ⊆ GG adj arrivals rank refuse m := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [GG_succ]; exact ih.trans (gstep_sub _ _ _ _ _ _)

theorem isMatching_insert {n : ℕ} {M : Finset (Fin n × Fin n)} (hM : IsMatching M)
    (p : Fin n × Fin n) (h1 : ∀ e ∈ M, e.1 ≠ p.1) (h2 : ∀ e ∈ M, e.2 ≠ p.2) :
    IsMatching (insert p M) := by
  constructor
  · intro e he f hf hef
    rw [Finset.mem_insert] at he hf
    rcases he with rfl | he <;> rcases hf with rfl | hf
    · rfl
    · exact absurd hef.symm (h1 f hf)
    · exact absurd hef (h1 e he)
    · exact hM.1 e he f hf hef
  · intro e he f hf hef
    rw [Finset.mem_insert] at he hf
    rcases he with rfl | he <;> rcases hf with rfl | hf
    · rfl
    · exact absurd hef.symm (h2 f hf)
    · exact absurd hef (h2 e he)
    · exact hM.2 e he f hf hef

theorem GG_inv {n : ℕ} (adj : Fin n → Fin n → Prop)
    (arrivals rank : Equiv.Perm (Fin n))
    (refuse : ℕ → Finset (Fin n × Fin n) → Fin n → Bool) (k : ℕ) (hk : k ≤ n) :
    IsMatching (GG adj arrivals rank refuse k) ∧
    (∀ e ∈ GG adj arrivals rank refuse k, adj e.1 e.2) ∧
    (∀ e ∈ GG adj arrivals rank refuse k, ((arrivals.symm e.1 : Fin n) : ℕ) < k) := by
  induction k with
  | zero =>
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp [GG]
  | succ k ih =>
    obtain ⟨h1, h2, h3⟩ := ih (by omega)
    have ht : k < n := hk
    rw [GG_succ]
    rcases gstep_cases adj arrivals rank refuse _ k ht with h | ⟨r, hadj, hnm, _, h⟩
    · rw [h]
      exact ⟨h1, h2, fun e he => by have := h3 e he; omega⟩
    · rw [h]
      refine ⟨isMatching_insert h1 _ ?_ ?_, ?_, ?_⟩
      · intro e he heq
        have := h3 e he
        have h4 : arrivals.symm e.1 = ⟨k, ht⟩ := by
          rw [heq]; simp
        rw [h4] at this; simp at this
      · intro e he heq
        exact hnm ⟨e, he, heq⟩
      · intro e he
        rw [Finset.mem_insert] at he
        rcases he with rfl | he
        · exact hadj
        · exact h2 e he
      · intro e he
        rw [Finset.mem_insert] at he
        rcases he with rfl | he
        · simp
        · have := h3 e he; omega

theorem greedy_matching {n : ℕ} (adj : Fin n → Fin n → Prop)
    (arrivals rank : Equiv.Perm (Fin n))
    (refuse : ℕ → Finset (Fin n × Fin n) → Fin n → Bool) :
    IsMatching (greedyRun adj arrivals rank refuse) :=
  (GG_inv adj arrivals rank refuse n le_rfl).1

theorem greedy_adj {n : ℕ} (adj : Fin n → Fin n → Prop)
    (arrivals rank : Equiv.Perm (Fin n))
    (refuse : ℕ → Finset (Fin n × Fin n) → Fin n → Bool) :
    ∀ e ∈ greedyRun adj arrivals rank refuse, adj e.1 e.2 :=
  (GG_inv adj arrivals rank refuse n le_rfl).2.1

/-- stability of the unrefused greedy run -/
theorem greedy_stable {n : ℕ} (adj : Fin n → Fin n → Prop)
    (arrivals rank : Equiv.Perm (Fin n)) :
    ∀ x y, adj x y →
      (x, y) ∈ greedyRun adj arrivals rank (fun _ _ _ => false) ∨
      (∃ y', (x, y') ∈ greedyRun adj arrivals rank (fun _ _ _ => false) ∧
        rank.symm y' < rank.symm y) ∨
      (∃ x', (x', y) ∈ greedyRun adj arrivals rank (fun _ _ _ => false) ∧
        arrivals.symm x' < arrivals.symm x) := by
  intro x y hxy
  set ref : ℕ → Finset (Fin n × Fin n) → Fin n → Bool := fun _ _ _ => false with href
  set t : Fin n := arrivals.symm x with ht
  have hx : arrivals ⟨t, t.2⟩ = x := by simp [ht]
  have hmono := GG_mono adj arrivals rank ref (show (t:ℕ)+1 ≤ n from t.2)
  have hmono0 := GG_mono adj arrivals rank ref (show (t:ℕ) ≤ n from t.2.le)
  rw [greedyRun_GG]
  by_cases hel : (adj x (rank (rank.symm y)) ∧
      ¬ secondMatched (GG adj arrivals rank ref t) (rank (rank.symm y)))
  · -- y eligible
    have hel' : ∃ r0 : Fin n, adj (arrivals ⟨t, t.2⟩) (rank r0) ∧
        ¬ secondMatched (GG adj arrivals rank ref t) (rank r0) := by
      rw [hx]; exact ⟨_, hel⟩
    obtain ⟨r, hadj, hnm, hmin, h⟩ := gstep_elig adj arrivals rank (GG adj arrivals rank ref t) t t.2 hel'
    · have hle := hmin _ (by rw [hx]; exact hel)
      rw [hx] at h hadj
      have hmem : (x, rank r) ∈ GG adj arrivals rank ref (t+1) := by
        rw [GG_succ, h]; exact Finset.mem_insert_self _ _
      rcases hle.lt_or_eq with hlt | heq
      · right; left; exact ⟨rank r, hmono hmem, by simpa using hlt⟩
      · left; rw [heq] at hmem; simp at hmem; exact hmono hmem
  · right; right
    have hsm : secondMatched (GG adj arrivals rank ref t) y := by
      by_contra hc
      apply hel
      simp only [Equiv.apply_symm_apply]
      exact ⟨hxy, hc⟩
    obtain ⟨e, he, rfl⟩ := hsm
    refine ⟨e.1, ?_, ?_⟩
    · have := hmono0 he; simpa using this
    · have := (GG_inv adj arrivals rank ref t t.2.le).2.2 e he
      exact Fin.lt_def.mpr this


theorem GG_snd_sub {n : ℕ} (adj : Fin n → Fin n → Prop)
    (arrivals rank : Equiv.Perm (Fin n))
    (refuse : ℕ → Finset (Fin n × Fin n) → Fin n → Bool) (k : ℕ) (hk : k ≤ n) :
    (GG adj arrivals rank refuse k).image Prod.snd ⊆
      (GG adj arrivals rank (fun _ _ _ => false) k).image Prod.snd := by
  induction k with
  | zero => simp [GG]
  | succ k ih =>
    have ih := ih (by omega)
    have ht : k < n := hk
    rw [GG_succ, GG_succ]
    set S := GG adj arrivals rank refuse k with hS
    set T := GG adj arrivals rank (fun _ _ _ => false) k with hT
    rcases gstep_cases adj arrivals rank refuse S k ht with h | ⟨r, hadj, hnm, hmin, h⟩
    · rw [h]
      exact ih.trans (Finset.image_subset_image (gstep_sub _ _ _ _ _ _))
    · rw [h]
      intro c hc
      rw [Finset.mem_image] at hc
      obtain ⟨e, he, rfl⟩ := hc
      rw [Finset.mem_insert] at he
      rcases he with rfl | he
      · by_cases hsm : secondMatched T (rank r)
        · obtain ⟨e', he', h'⟩ := hsm
          exact Finset.mem_image.mpr ⟨e', gstep_sub _ _ _ _ _ _ he', h'⟩
        · obtain ⟨r', hadj', hnm', hmin', h'⟩ :=
            gstep_elig adj arrivals rank T k ht ⟨r, hadj, hsm⟩
          have hr' : r' ≤ r := hmin' r ⟨hadj, hsm⟩
          have hr : r ≤ r' := by
            apply hmin r'
            refine ⟨hadj', ?_⟩
            rintro ⟨e', he', h''⟩
            have h3 : (rank r') ∈ T.image Prod.snd :=
              ih (Finset.mem_image.mpr ⟨e', he', h''⟩)
            obtain ⟨e'', he'', h4⟩ := Finset.mem_image.mp h3
            exact hnm' ⟨e'', he'', h4⟩
          have : r = r' := le_antisymm hr hr'
          rw [h', this]
          exact Finset.mem_image.mpr ⟨_, Finset.mem_insert_self _ _, rfl⟩
      · have := ih (Finset.mem_image.mpr ⟨e, he, rfl⟩)
        exact Finset.image_subset_image (gstep_sub _ _ _ _ _ _) this


theorem kvv_l2_core {n : ℕ} (adj : Fin n → Fin n → Prop)
    (boyOrder girlRank : Equiv.Perm (Fin n))
    (refuse : ℕ → Finset (Fin n × Fin n) → Fin n → Bool) :
    ((greedyRun adj boyOrder girlRank refuse).image Prod.snd) ⊆
    ((greedyRun adj boyOrder girlRank (fun _ _ _ => false)).image Prod.snd) :=
  GG_snd_sub adj boyOrder girlRank refuse n le_rfl

theorem card_eq_image_snd {n : ℕ} {M : Finset (Fin n × Fin n)} (hM : IsMatching M) :
    (M.image Prod.snd).card = M.card :=
  Finset.card_image_of_injOn (fun e he f hf h => hM.2 e he f hf h)

theorem card_eq_image_fst {n : ℕ} {M : Finset (Fin n × Fin n)} (hM : IsMatching M) :
    (M.image Prod.fst).card = M.card :=
  Finset.card_image_of_injOn (fun e he f hf h => hM.1 e he f hf h)

theorem greedy_card_le {n : ℕ} (adj : Fin n → Fin n → Prop)
    (arrivals rank : Equiv.Perm (Fin n))
    (refuse : ℕ → Finset (Fin n × Fin n) → Fin n → Bool) :
    (greedyRun adj arrivals rank refuse).card ≤
      (greedyRun adj arrivals rank (fun _ _ _ => false)).card := by
  rw [← card_eq_image_snd (greedy_matching adj arrivals rank refuse),
    ← card_eq_image_snd (greedy_matching adj arrivals rank (fun _ _ _ => false))]
  exact Finset.card_le_card (kvv_l2_core adj arrivals rank refuse)

theorem kvv_l5_core {n : ℕ} (adj : Fin n → Fin n → Prop)
    (rowOrder : Equiv.Perm (Fin n)) :
    (earlyMatching adj rowOrder).card ≤ (rowRankingMatching adj rowOrder).card := by
  unfold earlyMatching rowRankingMatching
  exact greedy_card_le _ _ _ _

theorem kvv_l4_core {n : ℕ} (M : Finset (Fin n × Fin n))
    (hM : IsMatching M)
    (hCover : ∀ i : Fin n, firstMatched M i ∨ secondMatched M i) :
    (M.card : ℝ) = ((n : ℝ) + (doubleCovered M).card) / 2 := by
  classical
  have hU : M.image Prod.fst ∪ M.image Prod.snd = Finset.univ := by
    ext i
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, iff_true]
    rcases hCover i with ⟨e, he, h⟩ | ⟨e, he, h⟩
    · exact Or.inl ⟨e, he, h⟩
    · exact Or.inr ⟨e, he, h⟩
  have hI : M.image Prod.fst ∩ M.image Prod.snd = doubleCovered M := by
    ext i
    simp [doubleCovered, firstMatched, secondMatched]
  have := Finset.card_union_add_card_inter (M.image Prod.fst) (M.image Prod.snd)
  rw [hU, hI, card_eq_image_fst hM, card_eq_image_snd hM, Finset.card_univ,
    Fintype.card_fin] at this
  have h2 : ((n + (doubleCovered M).card : ℕ) : ℝ) = ((M.card + M.card : ℕ) : ℝ) := by
    rw [this]
  push_cast at h2
  linarith

theorem kvv_cor_core {n : ℕ} (adj : Fin n → Fin n → Prop)
    (hdiag : ∀ i, adj i i)
    (hupper : ∀ i j, adj i j → i ≤ j) :
    rowRankingExpectation adj = (n : ℝ) / 2 +
      (1 / 2 : ℝ) * ((n.factorial : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin n),
          ((doubleCovered (rowRankingMatching adj σ)).card : ℝ)) := by
  have hc : ∀ σ : Equiv.Perm (Fin n),
      ((rowRankingMatching adj σ).card : ℝ) =
        (n : ℝ) / 2 + (1 / 2) * ((doubleCovered (rowRankingMatching adj σ)).card : ℝ) := by
    intro σ
    have hm : IsMatching (rowRankingMatching adj σ) := greedy_matching _ _ _ _
    have := kvv_l4_core (rowRankingMatching adj σ) hm (by
      intro i
      rcases greedy_stable adj σ Fin.revPerm i i (hdiag i) with h | ⟨y', h, _⟩ | ⟨x', h, _⟩
      · exact Or.inl ⟨_, h, rfl⟩
      · exact Or.inl ⟨_, h, rfl⟩
      · exact Or.inr ⟨_, h, rfl⟩)
    rw [this]; ring
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  unfold rowRankingExpectation
  rw [Finset.sum_congr rfl (fun σ _ => hc σ), Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  simp only [nsmul_eq_mul]
  field_simp

/-- stability predicate -/
def Stab {n : ℕ} (adj : Fin n → Fin n → Prop) (b g : Fin n → Fin n)
    (M : Finset (Fin n × Fin n)) : Prop :=
  IsMatching M ∧ (∀ e ∈ M, adj e.1 e.2) ∧
  ∀ x y, adj x y → (x, y) ∈ M ∨ (∃ y', (x, y') ∈ M ∧ g y' < g y) ∨
    ∃ x', (x', y) ∈ M ∧ b x' < b x

theorem stab_sub {n : ℕ} (adj : Fin n → Fin n → Prop) (b g : Fin n → Fin n)
    {M N : Finset (Fin n × Fin n)} (hM : Stab adj b g M) (hN : Stab adj b g N) :
    M ⊆ N := by
  classical
  obtain ⟨hMm, hMa, hMs⟩ := hM
  obtain ⟨hNm, hNa, hNs⟩ := hN
  by_contra hne
  rw [Finset.not_subset] at hne
  have hD : (M.filter (fun e => e ∉ N)).Nonempty := by
    obtain ⟨e, he, hn⟩ := hne
    exact ⟨e, Finset.mem_filter.mpr ⟨he, hn⟩⟩
  obtain ⟨e, heD, hmin⟩ := Finset.exists_min_image _
    (fun e : Fin n × Fin n => ((b e.1 : Fin n) : ℕ) + ((g e.2 : Fin n) : ℕ)) hD
  obtain ⟨heM, heN⟩ := Finset.mem_filter.mp heD
  obtain ⟨x, y⟩ := e
  simp only at hmin
  rcases hNs x y (hMa _ heM) with h | ⟨y', hy'N, hlt⟩ | ⟨x', hx'N, hlt⟩
  · exact heN h
  · have hlt' := Fin.lt_def.mp hlt
    have hy'M : (x, y') ∉ M := by
      intro h
      have := hMm.1 _ h _ heM rfl
      have h2 : y' = y := congrArg Prod.snd this
      subst h2
      exact lt_irrefl _ hlt
    rcases hMs x y' (hNa _ hy'N) with h | ⟨y'', hy''M, hlt2⟩ | ⟨x'', hx''M, hlt2⟩
    · exact hy'M h
    · have := hMm.1 _ hy''M _ heM rfl
      have h2 : y'' = y := congrArg Prod.snd this
      subst h2
      have := Fin.lt_def.mp hlt2
      omega
    · have hx''N : (x'', y') ∉ N := by
        intro h
        have := hNm.2 _ h _ hy'N rfl
        have h2 : x'' = x := congrArg Prod.fst this
        subst h2
        exact lt_irrefl _ hlt2
      have := hmin _ (Finset.mem_filter.mpr ⟨hx''M, hx''N⟩)
      have h3 := Fin.lt_def.mp hlt2
      simp only at this
      omega
  · have hlt' := Fin.lt_def.mp hlt
    have hx'M : (x', y) ∉ M := by
      intro h
      have := hMm.2 _ h _ heM rfl
      have h2 : x' = x := congrArg Prod.fst this
      subst h2
      exact lt_irrefl _ hlt
    rcases hMs x' y (hNa _ hx'N) with h | ⟨y'', hy''M, hlt2⟩ | ⟨x'', hx''M, hlt2⟩
    · exact hx'M h
    · have hy''N : (x', y'') ∉ N := by
        intro h
        have := hNm.1 _ h _ hx'N rfl
        have h2 : y'' = y := congrArg Prod.snd this
        subst h2
        exact lt_irrefl _ hlt2
      have := hmin _ (Finset.mem_filter.mpr ⟨hy''M, hy''N⟩)
      have h3 := Fin.lt_def.mp hlt2
      simp only at this
      omega
    · have := hMm.2 _ hx''M _ heM rfl
      have h2 : x'' = x := congrArg Prod.fst this
      subst h2
      have := Fin.lt_def.mp hlt2
      omega

theorem kvv_l1_core {n : ℕ} (adj : Fin n → Fin n → Prop)
    (boyOrder girlOrder : Equiv.Perm (Fin n)) :
    (greedyRun (fun g b => adj b g) girlOrder boyOrder
      (fun _ _ _ => false)).image Prod.swap =
    greedyRun adj boyOrder girlOrder (fun _ _ _ => false) := by
  classical
  set A := greedyRun adj boyOrder girlOrder (fun _ _ _ => false) with hA
  set B := greedyRun (fun g b => adj b g) girlOrder boyOrder (fun _ _ _ => false) with hB
  have hSA : Stab adj boyOrder.symm girlOrder.symm A :=
    ⟨greedy_matching _ _ _ _, greedy_adj _ _ _ _, greedy_stable adj boyOrder girlOrder⟩
  have hBm := greedy_matching (fun g b => adj b g) girlOrder boyOrder (fun _ _ _ => false)
  have hBa := greedy_adj (fun g b => adj b g) girlOrder boyOrder (fun _ _ _ => false)
  have hBs := greedy_stable (fun g b => adj b g) girlOrder boyOrder
  have hSB : Stab adj boyOrder.symm girlOrder.symm (B.image Prod.swap) := by
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · intro e he f hf hef
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp hf
      have := hBm.2 a ha a' ha' hef
      rw [this]
    · intro e he f hf hef
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp hf
      have := hBm.1 a ha a' ha' hef
      rw [this]
    · intro e he
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
      exact hBa a ha
    · intro x y hxy
      rcases hBs y x hxy with h | ⟨b', hb', hlt⟩ | ⟨g', hg', hlt⟩
      · left; exact Finset.mem_image.mpr ⟨_, h, rfl⟩
      · right; right
        exact ⟨b', Finset.mem_image.mpr ⟨_, hb', rfl⟩, hlt⟩
      · right; left
        exact ⟨g', Finset.mem_image.mpr ⟨_, hg', rfl⟩, hlt⟩
  exact Finset.Subset.antisymm (stab_sub adj _ _ hSB hSA) (stab_sub adj _ _ hSA hSB)

end KVVMatching.Ranking

open KVVMatching.Ranking


theorem solution {n : ℕ} (adj : Fin n → Fin n → Prop)
    (hdiag : ∀ i, adj i i)
    (hupper : ∀ i j, adj i j → i ≤ j)
    (M : Finset (Fin n × Fin n))
    (hM : IsMatching M)
    (hEdges : ∀ e ∈ M, adj e.1 e.2)
    (hCover : ∀ i : Fin n, firstMatched M i ∨ secondMatched M i) :
    (M.card : ℝ) = ((n : ℝ) + (doubleCovered M).card) / 2 := by
  exact kvv_l4_core M hM hCover
