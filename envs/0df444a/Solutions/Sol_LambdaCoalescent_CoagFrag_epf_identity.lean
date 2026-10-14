-- Prove2me | solution 1 for LambdaCoalescent.CoagFrag.epf_identity
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T00:28:49.533431+00:00
-- url     : https://prove2.me/submissions/286f9fd3-1904-48fd-9ec4-c9ba47c05f9f

import Mathlib
import Definitions.Def_LambdaCoalescent_CoagFrag_Setting



namespace LambdaCoalescent.CoagFrag

open Classical

/-! ### algebra -/

lemma cf_prodIco (α θ : ℝ) (hα : α ≠ 0) (c : ℕ) :
    ∏ i ∈ Finset.Ico 1 c, (θ + (i : ℝ) * α) = α ^ (c - 1) * (ascPochhammer ℝ (c - 1)).eval (θ / α + 1) := by
  induction c with
  | zero => simp
  | succ c ih =>
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · simp
    rw [Finset.prod_Ico_succ_top (by omega), ih]
    obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
    simp only [Nat.add_sub_cancel, ascPochhammer_succ_eval, pow_succ]
    push_cast
    field_simp
    ring

lemma cf_prodIco2 (α β θ : ℝ) (hα : α ≠ 0) (c : ℕ) :
    ∏ i ∈ Finset.Ico 1 c, (θ / α + (i : ℝ) * β) = (∏ i ∈ Finset.Ico 1 c, (θ + (i : ℝ) * (α * β))) / α ^ (c - 1) := by
  have : ∀ i ∈ Finset.Ico 1 c, (θ / α + (i : ℝ) * β) = (θ + (i : ℝ) * (α * β)) / α := by
    intro i _; field_simp
  rw [Finset.prod_congr rfl this, Finset.prod_div_distrib, Finset.prod_const, Nat.card_Ico]

lemma cf_card_sum (F : Multiset (Multiset ℕ)) (hF : ∀ m ∈ F, m ≠ 0) :
    (F.map Multiset.card).sum = (F.map (fun m => Multiset.card m - 1)).sum + Multiset.card F := by
  induction F using Multiset.induction_on with
  | empty => simp
  | cons a F ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    have ha : Multiset.card a ≠ 0 := by simpa using hF a (Multiset.mem_cons_self a F)
    rw [ih (fun m hm => hF m (Multiset.mem_cons_of_mem hm))]
    omega

lemma cf_prod_pow (α : ℝ) (F : Multiset (Multiset ℕ)) :
    (F.map (fun m => α ^ (Multiset.card m - 1))).prod = α ^ (F.map (fun m => Multiset.card m - 1)).sum := by
  induction F using Multiset.induction_on with
  | empty => simp
  | cons a F ih => simp [ih, pow_add]

lemma cf_alg (α β θ : ℝ) (hα : α ≠ 0) (F : Multiset (Multiset ℕ)) (hF : ∀ m ∈ F, m ≠ 0)
    (hQ : (ascPochhammer ℝ (Multiset.card F.join - 1)).eval (θ / α + 1) ≠ 0)
    (hH : ∀ m ∈ F, (ascPochhammer ℝ (m.sum - 1)).eval (1 - α * β) ≠ 0) :
    pdEPF α θ F.join * pdEPF β (θ / α) (F.map Multiset.card) =
      (F.map (pdEPF α (-(α * β)))).prod * pdEPF (α * β) θ (F.map Multiset.sum) := by
  rcases Multiset.empty_or_exists_mem F with rfl | ⟨m0, hm0⟩
  · simp [pdEPF]
  have hJ : 1 ≤ Multiset.card F := Multiset.card_pos_iff_exists_mem.2 ⟨m0, hm0⟩
  have hK : Multiset.card F.join - 1 = (F.map (fun m => Multiset.card m - 1)).sum + (Multiset.card F - 1) := by
    rw [Multiset.card_join, cf_card_sum F hF]; omega
  have hsum : F.join.sum = (F.map Multiset.sum).sum := Multiset.sum_join
  have hpow : α ^ ((F.map Multiset.card).sum - 1) =
      α ^ (F.map (fun m => Multiset.card m - 1)).sum * α ^ (Multiset.card F - 1) := by
    rw [← pow_add, ← hK, Multiset.card_join]
  have e1 : ∀ m : Multiset ℕ, ∏ i ∈ Finset.Ico 1 (Multiset.card m), (-(α * β) + (i : ℝ) * α) =
      α ^ (Multiset.card m - 1) * (ascPochhammer ℝ (Multiset.card m - 1)).eval (1 - β) := by
    intro m; rw [cf_prodIco α _ hα]; congr 2; field_simp; ring
  have hHp : (F.map (fun m => (ascPochhammer ℝ (m.sum - 1)).eval (1 - α * β))).prod ≠ 0 := by
    apply Multiset.prod_ne_zero
    intro h; obtain ⟨m, hm, h0⟩ := Multiset.mem_map.1 h; exact hH m hm h0
  rw [Multiset.card_join] at hQ
  unfold pdEPF
  rw [cf_prodIco α θ hα, cf_prodIco2 α β θ hα]
  simp only [e1, Multiset.card_map, hsum, Multiset.card_join]
  rw [Multiset.prod_map_mul, Multiset.prod_map_div, Multiset.prod_map_mul, cf_prod_pow, hpow,
    Multiset.map_join, Multiset.prod_join, Multiset.map_map, Multiset.map_map, Multiset.map_map]
  simp only [Function.comp_def]
  simp only [neg_add_eq_sub]
  generalize (∏ x ∈ Finset.Ico 1 (Multiset.card F), (θ + (x : ℝ) * (α * β))) = T
  generalize (F.map (fun m => (ascPochhammer ℝ (m.sum - 1)).eval (1 - α * β))).prod = H at hHp ⊢
  generalize (ascPochhammer ℝ ((F.map Multiset.card).sum - 1)).eval (θ / α + 1) = Q at hQ ⊢
  field_simp

/-! ### block combinatorics -/

noncomputable def cls {n : ℕ} (s : Setoid (Fin n)) (i : Fin n) : Finset (Fin n) := Finset.univ.filter (fun j => s i j)

lemma cf_blocks_eq {n : ℕ} (s : Setoid (Fin n)) : blocks s = Finset.univ.image (cls s) := rfl

lemma cf_mem_cls {n : ℕ} (s : Setoid (Fin n)) (i j : Fin n) : j ∈ cls s i ↔ s i j := by simp [cls]

lemma cf_cls_eq {n : ℕ} (s : Setoid (Fin n)) (i j : Fin n) : cls s i = cls s j ↔ s i j := by
  constructor
  · intro h; have : j ∈ cls s i := h ▸ (cf_mem_cls s j j).2 (s.refl j)
    exact (cf_mem_cls s i j).1 this
  · intro h; ext l; rw [cf_mem_cls, cf_mem_cls]
    exact ⟨fun h' => s.trans (s.symm h) h', fun h' => s.trans h h'⟩

lemma cf_mem_blocks {n : ℕ} (s : Setoid (Fin n)) (B : Finset (Fin n)) : B ∈ blocks s ↔ ∃ i, cls s i = B := by
  simp [cf_blocks_eq]

lemma cf_le {n : ℕ} {π₁ π₂ : Setoid (Fin n)} (h : π₁ ≤ π₂) {i j : Fin n} (hij : π₁ i j) : π₂ i j :=
  Setoid.le_def.1 h hij

lemma cf_filt {n : ℕ} (π₁ π₂ : Setoid (Fin n)) (h : π₁ ≤ π₂) (i : Fin n) :
    (blocks π₁).filter (fun A => A ⊆ cls π₂ i) = (cls π₂ i).image (cls π₁) := by
  ext A
  simp only [Finset.mem_filter, cf_mem_blocks, Finset.mem_image, cf_mem_cls]
  constructor
  · rintro ⟨⟨j, rfl⟩, hA⟩
    exact ⟨j, (cf_mem_cls _ _ _).1 (hA ((cf_mem_cls _ _ _).2 (π₁.refl j))), rfl⟩
  · rintro ⟨j, hj, rfl⟩
    refine ⟨⟨j, rfl⟩, fun l hl => ?_⟩
    rw [cf_mem_cls] at hl ⊢
    exact π₂.trans hj (cf_le h hl)

lemma cf_card_cls_sum {n : ℕ} (π₁ π₂ : Setoid (Fin n)) (h : π₁ ≤ π₂) (i : Fin n) :
    ∑ A ∈ (cls π₂ i).image (cls π₁), A.card = (cls π₂ i).card := by
  rw [Finset.card_eq_sum_card_image (cls π₁) (cls π₂ i)]
  apply Finset.sum_congr rfl
  intro A hA
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hA
  congr 1
  ext l
  simp only [Finset.mem_filter, cf_cls_eq, cf_mem_cls]
  rw [cf_mem_cls] at hj
  constructor
  · intro hl
    exact ⟨π₂.trans hj (cf_le h hl), π₁.symm hl⟩
  · rintro ⟨_, hl⟩; exact π₁.symm hl

lemma cf_coagCounts_eq {n : ℕ} (π₁ π₂ : Setoid (Fin n)) :
    coagCounts π₁ π₂ = (fragSizes π₁ π₂).map Multiset.card := by
  simp only [coagCounts, fragSizes, Multiset.map_map, Function.comp_def, Multiset.card_map]
  rfl

lemma cf_blockSizes2_eq {n : ℕ} (π₁ π₂ : Setoid (Fin n)) (h : π₁ ≤ π₂) :
    blockSizes π₂ = (fragSizes π₁ π₂).map Multiset.sum := by
  simp only [blockSizes, fragSizes, Multiset.map_map, Function.comp_def]
  apply Multiset.map_congr rfl
  intro B hB
  obtain ⟨i, rfl⟩ := (cf_mem_blocks _ _).1 hB
  rw [cf_filt π₁ π₂ h i, ← cf_card_cls_sum π₁ π₂ h i]
  rfl

lemma cf_frag_ne {n : ℕ} (π₁ π₂ : Setoid (Fin n)) (h : π₁ ≤ π₂) : ∀ m ∈ fragSizes π₁ π₂, m ≠ 0 := by
  intro m hm
  simp only [fragSizes, Multiset.mem_map] at hm
  obtain ⟨B, hB, rfl⟩ := hm
  obtain ⟨i, rfl⟩ := (cf_mem_blocks _ _).1 (by simpa using hB)
  rw [cf_filt π₁ π₂ h i]
  intro h0
  have := congrArg Multiset.card h0
  simp only [Multiset.card_map, Finset.card_val, Multiset.card_zero, Finset.card_eq_zero,
    Finset.image_eq_empty] at this
  have hi : i ∈ cls π₂ i := (cf_mem_cls _ _ _).2 (π₂.refl i)
  rw [this] at hi; simp at hi

lemma cf_blockSizes1_eq {n : ℕ} (π₁ π₂ : Setoid (Fin n)) (h : π₁ ≤ π₂) :
    blockSizes π₁ = (fragSizes π₁ π₂).join := by
  have hdisj : ((blocks π₂ : Set (Finset (Fin n)))).PairwiseDisjoint
      (fun B => (blocks π₁).filter (fun A => A ⊆ B)) := by
    intro B hB B' hB' hne
    simp only [Finset.mem_coe, cf_mem_blocks] at hB hB'
    obtain ⟨i, rfl⟩ := hB; obtain ⟨i', rfl⟩ := hB'
    rw [Function.onFun, cf_filt π₁ π₂ h, cf_filt π₁ π₂ h, Finset.disjoint_left]
    intro A hA hA'
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hA
    obtain ⟨j', hj', hjj⟩ := Finset.mem_image.1 hA'
    rw [cf_cls_eq] at hjj
    rw [cf_mem_cls] at hj hj'
    apply hne; rw [cf_cls_eq]
    exact π₂.trans hj (π₂.symm (π₂.trans hj' (cf_le h hjj)))
  have hU : (blocks π₂).disjiUnion (fun B => (blocks π₁).filter (fun A => A ⊆ B)) hdisj = blocks π₁ := by
    rw [Finset.disjiUnion_eq_biUnion]
    ext A
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · rintro ⟨B, _, hA, _⟩; exact hA
    · intro hA
      obtain ⟨j, rfl⟩ := (cf_mem_blocks _ _).1 hA
      refine ⟨cls π₂ j, (cf_mem_blocks _ _).2 ⟨j, rfl⟩, hA, fun l hl => ?_⟩
      rw [cf_mem_cls] at hl ⊢; exact cf_le h hl
  have hv := congrArg Finset.val hU
  rw [Finset.disjiUnion_val] at hv
  simp only [blockSizes, fragSizes, Multiset.join, ← hv]
  rw [Multiset.bind, Multiset.map_join, Multiset.map_map]
  rfl

theorem epf_identity_core (α β θ : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hθ : -(α * β) < θ) (n : ℕ) (π₁ π₂ : Setoid (Fin n)) (h : π₁ ≤ π₂) :
    pdEPF α θ (blockSizes π₁) * pdEPF β (θ / α) (coagCounts π₁ π₂) =
      ((fragSizes π₁ π₂).map (pdEPF α (-(α * β)))).prod * pdEPF (α * β) θ (blockSizes π₂) := by
  rw [cf_blockSizes1_eq π₁ π₂ h, cf_coagCounts_eq, cf_blockSizes2_eq π₁ π₂ h]
  apply cf_alg α β θ hα0.ne' _ (cf_frag_ne π₁ π₂ h)
  · apply ne_of_gt; apply ascPochhammer_pos
    have : -β < θ / α := by rw [lt_div_iff₀ hα0]; linarith
    linarith
  · intro m _; apply ne_of_gt; apply ascPochhammer_pos; nlinarith

end LambdaCoalescent.CoagFrag

open LambdaCoalescent.CoagFrag


theorem solution (α β θ : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hθ : -(α * β) < θ) (n : ℕ) (π₁ π₂ : Setoid (Fin n)) (h : π₁ ≤ π₂) :
    pdEPF α θ (blockSizes π₁) * pdEPF β (θ / α) (coagCounts π₁ π₂) =
      ((fragSizes π₁ π₂).map (pdEPF α (-(α * β)))).prod * pdEPF (α * β) θ (blockSizes π₂) := by
  exact epf_identity_core α β θ hα0 hα1 hβ0 hβ1 hθ n π₁ π₂ h
