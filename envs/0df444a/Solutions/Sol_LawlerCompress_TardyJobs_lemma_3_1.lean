-- Prove2me | solution 1 for LawlerCompress.TardyJobs.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-22T17:30:34.528234+00:00
-- url     : https://prove2.me/submissions/7a7cd9f8-b115-405e-8205-e19ccf0bb83a

import Definitions.Def_LawlerCompress_TardyJobs_Canonical

set_option autoImplicit false

namespace LawlerCompress.TardyJobs.L31

/-- `merge` keeps sortedness for a relation that is total only on distinct elements,
provided the two lists are disjoint. -/
theorem pw_merge {α : Type} (le : α → α → Bool)
    (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, a ≠ b → le a b ∨ le b a) :
    ∀ (l₁ l₂ : List α), (∀ x ∈ l₁, ∀ y ∈ l₂, x ≠ y) →
      l₁.Pairwise (le · ·) → l₂.Pairwise (le · ·) → (List.merge l₁ l₂ le).Pairwise (le · ·)
  | [], l₂, _, _, h₂ => by simpa using h₂
  | x :: l₁, [], _, h₁, _ => by simpa using h₁
  | x :: l₁, y :: l₂, hd, h₁, h₂ => by
    rw [List.cons_merge_cons]
    split <;> rename_i h
    · apply List.Pairwise.cons
      · intro z m
        rw [List.mem_merge, List.mem_cons] at m
        rcases m with (m|rfl|m)
        · exact List.rel_of_pairwise_cons h₁ m
        · exact h
        · exact trans _ _ _ h (List.rel_of_pairwise_cons h₂ m)
      · exact pw_merge le trans total l₁ (y :: l₂)
          (fun a ha b hb => hd a (List.mem_cons_of_mem _ ha) b hb) h₁.tail h₂
    · have hyx : le y x := by
        rcases total x y (hd x List.mem_cons_self y List.mem_cons_self) with h' | h'
        · exact absurd h' h
        · exact h'
      apply List.Pairwise.cons
      · intro z m
        rw [List.mem_merge, List.mem_cons] at m
        rcases m with (⟨rfl|m⟩|m)
        · exact hyx
        · exact trans _ _ _ hyx (List.rel_of_pairwise_cons h₁ m)
        · exact List.rel_of_pairwise_cons h₂ m
      · exact pw_merge le trans total (x :: l₁) l₂
          (fun a ha b hb => hd a ha b (List.mem_cons_of_mem _ hb)) h₁ h₂.tail

open List.MergeSort.Internal in
/-- `mergeSort` sorts a duplicate-free list for a strict total order. -/
theorem pw_mergeSort {α : Type} (le : α → α → Bool)
    (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, a ≠ b → le a b ∨ le b a) :
    ∀ (l : List α), l.Nodup → (List.mergeSort l le).Pairwise (le · ·)
  | [], _ => by simp
  | [a], _ => by simp
  | a :: b :: xs, hl => by
    rw [List.mergeSort]
    have e := splitInTwo_fst_append_splitInTwo_snd ⟨a :: b :: xs, rfl⟩
    have hn : ((splitInTwo ⟨a :: b :: xs, rfl⟩).1.1 ++
        (splitInTwo ⟨a :: b :: xs, rfl⟩).2.1).Nodup := by
      rw [e]; exact hl
    have : (splitInTwo ⟨a :: b :: xs, rfl⟩).1.1.length < xs.length + 1 + 1 := by
      simp [splitInTwo_fst]; omega
    have : (splitInTwo ⟨a :: b :: xs, rfl⟩).2.1.length < xs.length + 1 + 1 := by
      simp [splitInTwo_snd]; omega
    apply pw_merge le trans total
    · intro x hx y hy hxy
      subst hxy
      rw [List.mem_mergeSort] at hx hy
      exact List.disjoint_of_nodup_append hn hx hy
    · exact pw_mergeSort le trans total _ (List.nodup_append.mp hn).1
    · exact pw_mergeSort le trans total _ (List.nodup_append.mp hn).2.1
termination_by l => l.length

variable {m : ℕ} (I : Instance m)

theorem higher_irrefl (j : Fin I.n) : ¬ higher I j j := by
  unfold higher; omega

theorem higher_trans (a b c : Fin I.n) (h1 : higher I a b) (h2 : higher I b c) :
    higher I a c := by
  unfold higher at *
  rw [Fin.lt_def] at *
  omega

theorem higher_total (a b : Fin I.n) (h : a ≠ b) : higher I a b ∨ higher I b a := by
  unfold higher
  rw [Fin.lt_def, Fin.lt_def]
  have := Fin.val_ne_of_ne h
  omega

/-- Number of elements of `S` with higher priority than `j`. -/
def cnt (S : Finset (Fin I.n)) (j : Fin I.n) : ℕ := (S.filter (fun h => higher I h j)).card

/-- The `κ` highest-priority elements of `S`; `tbar` is `top` of the eligible set. -/
def top (κ : ℕ) (S : Finset (Fin I.n)) : Finset (Fin I.n) := S.filter (fun j => cnt I S j < κ)

theorem cnt_mono {S T : Finset (Fin I.n)} (h : S ⊆ T) (j : Fin I.n) : cnt I S j ≤ cnt I T j :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

theorem cnt_lt_of_higher {S : Finset (Fin I.n)} {j j' : Fin I.n} (hj' : j' ∈ S)
    (h : higher I j' j) : cnt I S j' < cnt I S j := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨j', by simp [hj', h], by simp [higher_irrefl]⟩
  · intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, higher_trans I _ _ _ hx.2 h⟩

theorem cnt_lt_card {S : Finset (Fin I.n)} {j : Fin I.n} (hj : j ∈ S) : cnt I S j < S.card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
  exact ⟨j, hj, by simp [higher_irrefl]⟩

theorem cnt_injOn (S : Finset (Fin I.n)) : Set.InjOn (cnt I S) S := by
  intro x hx y hy hxy
  by_contra hne
  rcases higher_total I x y hne with h | h
  · have := cnt_lt_of_higher I (Finset.mem_coe.mp hx) h; omega
  · have := cnt_lt_of_higher I (Finset.mem_coe.mp hy) h; omega

theorem image_cnt (S : Finset (Fin I.n)) : S.image (cnt I S) = Finset.range S.card := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    simpa using cnt_lt_card I hj
  · rw [Finset.card_image_of_injOn (cnt_injOn I S)]; simp

theorem card_top (κ : ℕ) (S : Finset (Fin I.n)) : (top I κ S).card = min κ S.card := by
  unfold top
  rw [← Finset.card_image_of_injOn (f := cnt I S)
    (fun x hx y hy h => cnt_injOn I S (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 h)]
  have : (S.filter (fun j => cnt I S j < κ)).image (cnt I S) =
      (Finset.range S.card).filter (· < κ) := by
    rw [← image_cnt I S, Finset.filter_image]
  rw [this]
  have : (Finset.range S.card).filter (· < κ) = Finset.range (min κ S.card) := by
    ext x; simp; omega
  rw [this]; simp

theorem tbar_eq (p t : ℕ) : tbar I p t = top I (kappa I p) (eligible I p t) := rfl

theorem d_le_dmax (j : Fin I.n) : I.d j ≤ dmax I :=
  Finset.le_sup (f := I.d) (Finset.mem_univ j)

theorem mem_cbar (j : Fin I.n) (t : ℕ) :
    t ∈ cbar I j ↔
      I.p j ≤ t ∧ t ≤ dmax I ∧ j ∈ top I (kappa I (I.p j)) (eligible I (I.p j) t) := by
  unfold cbar
  rw [Finset.mem_filter, Finset.mem_Icc, tbar_eq, and_assoc]

theorem a_eq_of_least (j : Fin I.n) (t0 : ℕ) (ht0 : t0 ≤ dmax I) (h0 : t0 ∈ cbar I j)
    (hlt : ∀ t < t0, t ∉ cbar I j) : a I j = t0 := by
  unfold a
  obtain ⟨k, hk⟩ : ∃ k, dmax I + 1 = t0 + (k + 1) := ⟨dmax I - t0, by omega⟩
  rw [hk, List.range_add, List.filter_append, List.range_succ_eq_map]
  have e1 : (List.range t0).filter (fun t => decide (t ∈ cbar I j)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro t ht
    simpa using hlt t (List.mem_range.mp ht)
  rw [e1]
  simp [h0]

theorem a_eq_default (j : Fin I.n) (h : ∀ t, t ∉ cbar I j) : a I j = I.d j + 1 := by
  unfold a
  have e1 : (List.range (dmax I + 1)).filter (fun t => decide (t ∈ cbar I j)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro t _
    simpa using h t
  rw [e1]; rfl

/-- A job leaving the top-κ when `i` is inserted has canonical endpoint `d_i + 1`. -/
theorem a_evict (hedd : EDD I) (i low : Fin I.n) (S : Finset (Fin I.n))
    (hS : ∀ g, g ∈ S ↔ I.p g = I.p i ∧ i < g)
    (hlow_p : I.p low = I.p i) (hlow : low = i ∨ (low ∈ S ∧ cnt I S low < kappa I (I.p i)))
    (hbig : kappa I (I.p i) ≤ cnt I (insert i S) low) : a I low = I.d i + 1 := by
  have key1 : ∀ t ≤ I.d i, insert i S ⊆ eligible I (I.p i) t := by
    intro t ht g hg
    unfold eligible
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases Finset.mem_insert.mp hg with rfl | hg
    · exact ⟨rfl, ht⟩
    · obtain ⟨h1, h2⟩ := (hS g).mp hg
      exact ⟨h1, le_trans ht (hedd (le_of_lt h2))⟩
  have notin : ∀ t ≤ I.d i, t ∉ cbar I low := by
    intro t ht hc
    rw [mem_cbar, hlow_p] at hc
    have := (Finset.mem_filter.mp hc.2.2).2
    have := cnt_mono I (key1 t ht) low
    omega
  have hil : i ≤ low := by
    rcases hlow with rfl | ⟨h, _⟩
    · exact le_rfl
    · exact le_of_lt ((hS low).mp h).2
  have hdil : I.d i ≤ I.d low := hedd hil
  by_cases hd : I.d low ≤ I.d i
  · rw [a_eq_default]
    · omega
    intro t
    by_cases ht : t ≤ I.d i
    · exact notin t ht
    · intro hc
      rw [mem_cbar] at hc
      have := (Finset.mem_filter.mp (Finset.mem_filter.mp hc.2.2).1).2.2
      omega
  · have hne : low ≠ i := by rintro rfl; exact hd le_rfl
    obtain ⟨hlS, hcS⟩ := hlow.resolve_left hne
    have helS : eligible I (I.p i) (I.d i + 1) ⊆ S := by
      intro g hg
      unfold eligible at hg
      rw [Finset.mem_filter] at hg
      rw [hS]
      refine ⟨hg.2.1, ?_⟩
      by_contra hc
      have := hedd (not_lt.mp hc)
      omega
    apply a_eq_of_least
    · exact le_trans (by omega) (d_le_dmax I low)
    · rw [mem_cbar, hlow_p]
      refine ⟨by have := I.p_le_d i; omega, le_trans (by omega) (d_le_dmax I low), ?_⟩
      unfold top
      rw [Finset.mem_filter]
      refine ⟨?_, lt_of_le_of_lt (cnt_mono I helS low) hcS⟩
      unfold eligible
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hlow_p, by omega⟩
    · intro t ht
      exact notin t (by omega)

/-- A job in the top-κ of its whole group has canonical endpoint `p_j`. -/
theorem a_top (j : Fin I.n)
    (h : j ∈ top I (kappa I (I.p j)) (Finset.univ.filter (fun g => I.p g = I.p j))) :
    a I j = I.p j := by
  have he : eligible I (I.p j) (I.p j) = Finset.univ.filter (fun g => I.p g = I.p j) := by
    ext g
    unfold eligible
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_left_iff_imp]
    intro hg
    have := I.p_le_d g
    omega
  have hpd : I.p j ≤ dmax I := le_trans (I.p_le_d j) (d_le_dmax I j)
  apply a_eq_of_least I j _ hpd
  · rw [mem_cbar, he]
    exact ⟨le_rfl, hpd, h⟩
  · intro t ht hc
    rw [mem_cbar] at hc
    omega

/-- One heap step preserves the invariant: heap = top-κ of the processed suffix,
and every processed job outside the heap stores its canonical endpoint. -/
theorem step (hedd : EDD I) (i : Fin I.n) (S : Finset (Fin I.n))
    (hS : ∀ g, g ∈ S ↔ I.p g = I.p i ∧ i < g) (s : Finset (Fin I.n) × (Fin I.n → ℕ))
    (h1 : s.1 = top I (kappa I (I.p i)) S) (h2 : ∀ j ∈ S, j ∉ s.1 → s.2 j = a I j) :
    (heapStep I (I.p i) s i).1 = top I (kappa I (I.p i)) (insert i S) ∧
      ∀ j ∈ insert i S, j ∉ (heapStep I (I.p i) s i).1 →
        (heapStep I (I.p i) s i).2 j = a I j := by
  set κ := kappa I (I.p i) with hκ
  obtain ⟨H, f⟩ := s
  simp only at h1 h2
  have hiS : i ∉ S := fun h => lt_irrefl i ((hS i).mp h).2
  have hHS : H ⊆ S := by rw [h1]; exact Finset.filter_subset _ _
  have hiH : i ∉ H := fun h => hiS (hHS h)
  have hcH : H.card = min κ S.card := by rw [h1]; exact card_top I κ S
  have hcins : (insert i H).card = H.card + 1 := Finset.card_insert_of_notMem hiH
  have hcS' : (insert i S).card = S.card + 1 := Finset.card_insert_of_notMem hiS
  unfold heapStep
  simp only
  split_ifs with hc
  · -- eviction
    set L := ((List.finRange I.n).filter (· ∈ insert i H)).mergeSort
      (fun x y => decide (higher I y x)) with hL
    have hmemL : ∀ x, x ∈ L ↔ x ∈ insert i H := by
      intro x; rw [hL, List.mem_mergeSort, List.mem_filter]; simp
    have hpw : L.Pairwise (fun x y => decide (higher I y x) = true) := by
      apply pw_mergeSort
      · intro a b c hab hbc
        simp only [decide_eq_true_eq] at *
        exact higher_trans I _ _ _ hbc hab
      · intro a b hab
        simp only [decide_eq_true_eq]
        rcases higher_total I a b hab with h | h
        · exact Or.inr h
        · exact Or.inl h
      · exact (List.nodup_finRange _).filter _
    obtain ⟨low, T, hLT⟩ : ∃ low T, L = low :: T := by
      cases hc' : L with
      | nil =>
        have := (hmemL i).mpr (Finset.mem_insert_self _ _); rw [hc'] at this; simp at this
      | cons x T => exact ⟨x, T, rfl⟩
    rw [hLT]
    simp only [List.headD_cons]
    have hlowmem : low ∈ insert i H := (hmemL low).mp (by rw [hLT]; exact List.mem_cons_self)
    have hlowmin : ∀ y ∈ insert i H, y ≠ low → higher I y low := by
      intro y hy hne
      rw [← hmemL, hLT, List.mem_cons] at hy
      rw [hLT, List.pairwise_cons] at hpw
      have := hpw.1 y (hy.resolve_left hne)
      simpa using this
    have hHk : H.card = κ := by omega
    have hcerase : ((insert i H).erase low).card = κ := by
      rw [Finset.card_erase_of_mem hlowmem]; omega
    have hctop : (top I κ (insert i S)).card = κ := by
      rw [card_top, hcS']; omega
    have hbig : κ ≤ cnt I (insert i S) low := by
      rw [← hcerase]
      apply Finset.card_le_card
      intro y hy
      rw [Finset.mem_erase] at hy
      rw [Finset.mem_filter]
      refine ⟨?_, hlowmin y hy.2 hy.1⟩
      rcases Finset.mem_insert.mp hy.2 with rfl | h
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (hHS h)
    have hsub : top I κ (insert i S) ⊆ (insert i H).erase low := by
      intro j hj
      unfold top at hj
      rw [Finset.mem_filter] at hj
      rw [Finset.mem_erase]
      refine ⟨?_, ?_⟩
      · rintro rfl; omega
      · rcases Finset.mem_insert.mp hj.1 with rfl | hjS
        · exact Finset.mem_insert_self _ _
        · apply Finset.mem_insert_of_mem
          rw [h1]
          unfold top
          rw [Finset.mem_filter]
          exact ⟨hjS, lt_of_le_of_lt (cnt_mono I (Finset.subset_insert _ _) j) hj.2⟩
    have heq : top I κ (insert i S) = (insert i H).erase low :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    refine ⟨heq.symm, ?_⟩
    intro j hj hjn
    by_cases hjl : j = low
    · subst hjl
      rw [Function.update_self]
      symm
      apply a_evict I hedd i j S hS
      · rcases Finset.mem_insert.mp hlowmem with rfl | h
        · rfl
        · exact ((hS j).mp (hHS h)).1
      · rcases Finset.mem_insert.mp hlowmem with h | h
        · exact Or.inl h
        · right
          rw [h1] at h
          unfold top at h
          exact Finset.mem_filter.mp h
      · exact hbig
    · rw [Function.update_of_ne hjl]
      have hjn' : j ∉ insert i H := fun h => hjn (Finset.mem_erase.mpr ⟨hjl, h⟩)
      rcases Finset.mem_insert.mp hj with rfl | hjS
      · exact absurd (Finset.mem_insert_self _ _) hjn'
      · exact h2 j hjS (fun h => hjn' (Finset.mem_insert_of_mem h))
  · have hHeq : H = S := Finset.eq_of_subset_of_card_le hHS (by omega)
    subst hHeq
    have htop : top I κ (insert i H) = insert i H := by
      unfold top
      apply Finset.filter_true_of_mem
      intro j hj
      have := cnt_lt_card I hj
      omega
    refine ⟨htop.symm, ?_⟩
    intro j hj hjn
    exact absurd hj hjn

/-- The invariant along the reverse traversal of an upward-closed, increasing list. -/
theorem fold (hedd : EDD I) (p : ℕ) :
    ∀ (l : List (Fin I.n)), l.Pairwise (· < ·) → (∀ x ∈ l, I.p x = p) →
      (∀ g x, x ∈ l → I.p g = p → x ≤ g → g ∈ l) →
      (l.foldr (fun j s => heapStep I p s j) (∅, fun j => I.d j + 1)).1 =
          top I (kappa I p) l.toFinset ∧
        ∀ j ∈ l.toFinset, j ∉ (l.foldr (fun j s => heapStep I p s j) (∅, fun j => I.d j + 1)).1 →
          (l.foldr (fun j s => heapStep I p s j) (∅, fun j => I.d j + 1)).2 j = a I j
  | [], _, _, _ => ⟨by unfold top; rw [List.toFinset_nil, Finset.filter_empty]; rfl, by simp⟩
  | x :: l', hpw, hp, hcl => by
    rw [List.pairwise_cons] at hpw
    have hcl' : ∀ g x', x' ∈ l' → I.p g = p → x' ≤ g → g ∈ l' := by
      intro g x' hx' hg hle
      have := hcl g x' (List.mem_cons_of_mem _ hx') hg hle
      rcases List.mem_cons.mp this with rfl | h
      · exact absurd (lt_of_lt_of_le (hpw.1 x' hx') hle) (lt_irrefl _)
      · exact h
    obtain ⟨ih1, ih2⟩ := fold hedd p l' hpw.2 (fun y hy => hp y (List.mem_cons_of_mem _ hy)) hcl'
    have hxp : I.p x = p := hp x List.mem_cons_self
    subst hxp
    have hS : ∀ g, g ∈ l'.toFinset ↔ I.p g = I.p x ∧ x < g := by
      intro g
      rw [List.mem_toFinset]
      constructor
      · intro hg
        exact ⟨hp g (List.mem_cons_of_mem _ hg), hpw.1 g hg⟩
      · rintro ⟨hg, hlt⟩
        rcases List.mem_cons.mp (hcl g x List.mem_cons_self hg (le_of_lt hlt)) with rfl | h
        · exact absurd hlt (lt_irrefl _)
        · exact h
    rw [List.foldr_cons, List.toFinset_cons]
    exact step I hedd x l'.toFinset hS _ ih1 ih2

end LawlerCompress.TardyJobs.L31

open LawlerCompress.TardyJobs LawlerCompress.TardyJobs.L31 in
theorem solution {m : ℕ} (hm : 1 ≤ m) (I : Instance m)
    (hn : 1 ≤ I.n) (hedd : EDD I) :
    ∀ j : Fin I.n, heapEndpoints I j = a I j := by
  intro j
  unfold heapEndpoints heapGroup
  rw [List.foldl_reverse]
  set jobs := (List.finRange I.n).filter (fun g => decide (I.p g = I.p j)) with hjobs
  have hpw : jobs.Pairwise (· < ·) := (List.pairwise_lt_finRange I.n).filter _
  have hp : ∀ x ∈ jobs, I.p x = I.p j := by
    intro x hx; rw [hjobs, List.mem_filter] at hx; simpa using hx.2
  have hcl : ∀ g x, x ∈ jobs → I.p g = I.p j → x ≤ g → g ∈ jobs := by
    intro g x _ hg _; rw [hjobs, List.mem_filter]; simpa using hg
  obtain ⟨h1, h2⟩ := fold I hedd (I.p j) jobs hpw hp hcl
  have hG : jobs.toFinset = Finset.univ.filter (fun g => I.p g = I.p j) := by
    ext g; rw [List.mem_toFinset, hjobs, List.mem_filter]; simp
  have hj : j ∈ jobs.toFinset := by rw [hG]; simp
  split_ifs with hin
  · rw [h1, hG] at hin
    exact (a_top I j hin).symm
  · exact h2 j hj hin
