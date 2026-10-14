-- Prove2me | solution 1 for LambdaCoalescent.CoagFrag.lemma_9_exists
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T00:56:32.484788+00:00
-- url     : https://prove2.me/submissions/7ba3fdb1-937c-43f6-9a01-7555d41a202b

import Mathlib
import Definitions.Def_LambdaCoalescent_CoagFrag_Setting



namespace LambdaCoalescent.CoagFrag

open MeasureTheory Classical


lemma cf_meas_rel (i j : ℕ) : MeasurableSet {π : LambdaCoalescent.Rates.PInf | π.r i j} := by
  have hφ : Measurable (fun π : LambdaCoalescent.Rates.PInf => fun p : ℕ × ℕ => π.r p.1 p.2) :=
    Measurable.of_comap_le le_rfl
  exact measurableSet_setOfPred.2 ((measurable_pi_apply (i, j)).comp hφ)

lemma cf_restrict_eq_iff (n : ℕ) (π : Setoid ℕ) (s : Setoid (Fin n)) :
    restrict n π = s ↔ ∀ i j : Fin n, (π.r i j ↔ s i j) := by
  constructor
  · rintro rfl i j; exact Iff.rfl
  · intro h; exact Setoid.ext h

lemma cf_meas_restrict_set (n : ℕ) (s : Setoid (Fin n)) :
    MeasurableSet {π : LambdaCoalescent.Rates.PInf | restrict n π = s} := by
  have : {π : LambdaCoalescent.Rates.PInf | restrict n π = s} =
      ⋂ i : Fin n, ⋂ j : Fin n, {π : LambdaCoalescent.Rates.PInf | π.r i j ↔ s i j} := by
    ext π; simp only [Set.mem_iInter]; exact cf_restrict_eq_iff n π s
  rw [this]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
  by_cases h : s i j
  · simp only [h, iff_true]; exact cf_meas_rel i j
  · simp only [h, iff_false]; exact (cf_meas_rel i j).compl

lemma cf_measurable_restrict (n : ℕ) :
    Measurable (fun π : LambdaCoalescent.Rates.PInf => restrict n π) := by
  apply measurable_to_countable'
  intro s
  exact cf_meas_restrict_set n s

/-- pair restriction -/
def cyl2 (n : ℕ) (x : LambdaCoalescent.Rates.PInf × LambdaCoalescent.Rates.PInf) :
    Setoid (Fin n) × Setoid (Fin n) := (restrict n x.1, restrict n x.2)

lemma cf_measurable_cyl2 (n : ℕ) : Measurable (cyl2 n) :=
  ((cf_measurable_restrict n).comp measurable_fst).prodMk ((cf_measurable_restrict n).comp measurable_snd)

def cylC : Set (Set (LambdaCoalescent.Rates.PInf × LambdaCoalescent.Rates.PInf)) :=
  {S | ∃ n, ∃ A : Set (Setoid (Fin n) × Setoid (Fin n)), S = cyl2 n ⁻¹' A}

lemma cf_restrict_le (n N : ℕ) (h : n ≤ N) (π : Setoid ℕ) :
    restrict n π = (restrict N π).comap (Fin.castLE h) := rfl

lemma cf_cyl2_le (n N : ℕ) (h : n ≤ N) :
    cyl2 n = (fun st : Setoid (Fin N) × Setoid (Fin N) => (st.1.comap (Fin.castLE h), st.2.comap (Fin.castLE h))) ∘ cyl2 N := rfl

lemma cf_isPi : IsPiSystem cylC := by
  rintro _ ⟨n, A, rfl⟩ _ ⟨m, B, rfl⟩ _
  refine ⟨max n m, (fun st : Setoid (Fin (max n m)) × Setoid (Fin (max n m)) =>
      (st.1.comap (Fin.castLE (le_max_left n m)), st.2.comap (Fin.castLE (le_max_left n m)))) ⁻¹' A ∩
    (fun st : Setoid (Fin (max n m)) × Setoid (Fin (max n m)) =>
      (st.1.comap (Fin.castLE (le_max_right n m)), st.2.comap (Fin.castLE (le_max_right n m)))) ⁻¹' B, ?_⟩
  rfl

lemma cf_gen : (inferInstance : MeasurableSpace (LambdaCoalescent.Rates.PInf × LambdaCoalescent.Rates.PInf)) =
    MeasurableSpace.generateFrom cylC := by
  apply le_antisymm
  · have key : ∀ (f : LambdaCoalescent.Rates.PInf × LambdaCoalescent.Rates.PInf → LambdaCoalescent.Rates.PInf),
        (∀ i j : ℕ, ∃ n, ∃ A : Set (Setoid (Fin n) × Setoid (Fin n)), {x | (f x).r i j} = cyl2 n ⁻¹' A) →
        MeasurableSpace.comap f inferInstance ≤ MeasurableSpace.generateFrom cylC := by
      intro f hf
      show MeasurableSpace.comap f (MeasurableSpace.comap _ inferInstance) ≤ _
      rw [MeasurableSpace.comap_comp, MeasurableSpace.comap_le_iff_le_map]
      have : @Measurable _ _ (MeasurableSpace.generateFrom cylC) _
          ((fun π : LambdaCoalescent.Rates.PInf => fun p : ℕ × ℕ => π.r p.1 p.2) ∘ f) := by
        rw [@measurable_pi_iff]
        intro p
        apply (@measurableSet_setOfPred _ (MeasurableSpace.generateFrom cylC) _).1
        obtain ⟨n, A, hA⟩ := hf p.1 p.2
        apply MeasurableSpace.measurableSet_generateFrom
        exact ⟨n, A, hA⟩
      exact this
    refine sup_le (key Prod.fst ?_) (key Prod.snd ?_)
    · intro i j
      refine ⟨max i j + 1, {st | st.1 ⟨i, by omega⟩ ⟨j, by omega⟩}, ?_⟩
      ext x; rfl
    · intro i j
      refine ⟨max i j + 1, {st | st.2 ⟨i, by omega⟩ ⟨j, by omega⟩}, ?_⟩
      ext x; rfl
  · apply MeasurableSpace.generateFrom_le
    rintro _ ⟨n, A, rfl⟩
    exact cf_measurable_cyl2 n (MeasurableSet.of_discrete)

lemma cf_uniq (M Q : Measure (LambdaCoalescent.Rates.PInf × LambdaCoalescent.Rates.PInf)) [IsFiniteMeasure M]
    (h : ∀ n (s t : Setoid (Fin n)), M {x | restrict n x.1 = s ∧ restrict n x.2 = t} =
      Q {x | restrict n x.1 = s ∧ restrict n x.2 = t}) : M = Q := by
  have hC : ∀ S ∈ cylC, M S = Q S := by
    rintro _ ⟨n, A, rfl⟩
    have hmap : M.map (cyl2 n) = Q.map (cyl2 n) := by
      rw [Measure.ext_iff_singleton]
      rintro ⟨s, t⟩
      rw [Measure.map_apply (cf_measurable_cyl2 n) (MeasurableSet.of_discrete),
        Measure.map_apply (cf_measurable_cyl2 n) (MeasurableSet.of_discrete)]
      have : cyl2 n ⁻¹' {(s, t)} = {x | restrict n x.1 = s ∧ restrict n x.2 = t} := by
        ext x; simp [cyl2]
      rw [this]; exact h n s t
    rw [← Measure.map_apply (cf_measurable_cyl2 n) (MeasurableSet.of_discrete),
      ← Measure.map_apply (cf_measurable_cyl2 n) (MeasurableSet.of_discrete), hmap]
  refine ext_of_generate_finite cylC cf_gen cf_isPi hC ?_
  exact hC _ ⟨0, Set.univ, rfl⟩



lemma cf_L_le (π : Setoid ℕ) (i : ℕ) : leastElt π i ≤ i := Nat.find_min' _ (π.refl i)

lemma cf_L_rel (π : Setoid ℕ) (i : ℕ) : π (leastElt π i) i := Nat.find_spec (⟨i, π.refl i⟩ : ∃ m, π m i)

lemma cf_L_min (π : Setoid ℕ) (i m : ℕ) (h : π m i) : leastElt π i ≤ m := Nat.find_min' _ h

lemma cf_L_eq (π : Setoid ℕ) (i j : ℕ) (h : π i j) : leastElt π i = leastElt π j :=
  le_antisymm (cf_L_min π i _ (π.trans (cf_L_rel π j) (π.symm h)))
    (cf_L_min π j _ (π.trans (cf_L_rel π i) h))

lemma cf_L_fix (π : Setoid ℕ) (i : ℕ) : leastElt π (leastElt π i) = leastElt π i :=
  cf_L_eq π _ _ (cf_L_rel π i)

noncomputable def cfF (π : Setoid ℕ) (a : ℕ) : Finset ℕ := (Finset.range a).filter (fun m => leastElt π m = m)

lemma cf_bi_def (π : Setoid ℕ) (i : ℕ) : blockIndex π i = (cfF π (leastElt π i)).card := rfl

lemma cf_F_ssub (π : Setoid ℕ) (a b : ℕ) (hab : a < b) (ha : leastElt π a = a) : cfF π a ⊂ cfF π b := by
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨a, by simp [cfF, hab, ha], by simp [cfF]⟩
  · intro x hx; simp only [cfF, Finset.mem_filter, Finset.mem_range] at hx ⊢; exact ⟨by omega, hx.2⟩

lemma cf_bi_eq (π : Setoid ℕ) (i j : ℕ) (h : π i j) : blockIndex π i = blockIndex π j := by
  rw [cf_bi_def, cf_bi_def, cf_L_eq π i j h]

lemma cf_bi_inj (π : Setoid ℕ) (i j : ℕ) (h : blockIndex π i = blockIndex π j) : π i j := by
  rw [cf_bi_def, cf_bi_def] at h
  have hL : leastElt π i = leastElt π j := by
    rcases lt_trichotomy (leastElt π i) (leastElt π j) with hl | hl | hl
    · have := Finset.card_lt_card (cf_F_ssub π _ _ hl (cf_L_fix π i)); omega
    · exact hl
    · have := Finset.card_lt_card (cf_F_ssub π _ _ hl (cf_L_fix π j)); omega
  exact π.trans (π.symm (cf_L_rel π i)) (hL ▸ cf_L_rel π j)

lemma cf_bi_iff (π : Setoid ℕ) (i j : ℕ) : blockIndex π i = blockIndex π j ↔ π i j :=
  ⟨cf_bi_inj π i j, cf_bi_eq π i j⟩

lemma cf_L_local (π π' : Setoid ℕ) (n : ℕ) (h : ∀ a b, a < n → b < n → (π a b ↔ π' a b))
    (i : ℕ) (hi : i < n) : leastElt π i = leastElt π' i := by
  apply le_antisymm
  · apply cf_L_min; rw [h _ _ (by have := cf_L_le π' i; omega) hi]; exact cf_L_rel π' i
  · apply cf_L_min; rw [← h _ _ (by have := cf_L_le π i; omega) hi]; exact cf_L_rel π i

lemma cf_bi_local (π π' : Setoid ℕ) (n : ℕ) (h : ∀ a b, a < n → b < n → (π a b ↔ π' a b))
    (i : ℕ) (hi : i < n) : blockIndex π i = blockIndex π' i := by
  rw [cf_bi_def, cf_bi_def, cf_L_local π π' n h i hi]
  congr 1
  apply Finset.filter_congr
  intro m hm
  simp only [Finset.mem_range] at hm
  have := cf_L_le π' i
  rw [cf_L_local π π' n h m (by omega)]

noncomputable def cfK (π : Setoid ℕ) (n : ℕ) : ℕ := (cfF π n).card

lemma cf_bi_lt (π : Setoid ℕ) (n i : ℕ) (hi : i < n) : blockIndex π i < cfK π n := by
  rw [cf_bi_def, cfK]
  exact Finset.card_lt_card (cf_F_ssub π _ _ (lt_of_le_of_lt (cf_L_le π i) hi) (cf_L_fix π i))

lemma cf_bi_surj (π : Setoid ℕ) (n c : ℕ) (hc : c < cfK π n) : ∃ i, i < n ∧ blockIndex π i = c := by
  have hsub : (cfF π n).image (blockIndex π) ⊆ Finset.range (cfK π n) := by
    intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨m, hm, rfl⟩ := hx
    simp only [cfF, Finset.mem_filter, Finset.mem_range] at hm
    exact Finset.mem_range.2 (cf_bi_lt π n m hm.1)
  have hinj : Set.InjOn (blockIndex π) (cfF π n) := by
    intro a ha b hb hab
    simp only [cfF, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at ha hb
    have := cf_bi_inj π a b hab
    rw [← ha.2, ← hb.2]; exact cf_L_eq π a b this
  have heq : (cfF π n).image (blockIndex π) = Finset.range (cfK π n) := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [Finset.card_image_of_injOn hinj, Finset.card_range, cfK]
  have : c ∈ (cfF π n).image (blockIndex π) := by rw [heq]; exact Finset.mem_range.2 hc
  simp only [Finset.mem_image] at this
  obtain ⟨m, hm, rfl⟩ := this
  simp only [cfF, Finset.mem_filter, Finset.mem_range] at hm
  exact ⟨m, hm.1, rfl⟩

/-- canonical extension of a finite partition -/
noncomputable def cfExt {n : ℕ} (s : Setoid (Fin n)) : Setoid ℕ :=
  Setoid.ker (fun a : ℕ => if h : a < n then (Sum.inl (Quotient.mk s ⟨a, h⟩) : Quotient s ⊕ ℕ) else Sum.inr a)

lemma cf_ext_rel {n : ℕ} (s : Setoid (Fin n)) (a b : Fin n) : cfExt s a b ↔ s a b := by
  show (fun a : ℕ => if h : a < n then (Sum.inl (Quotient.mk s ⟨a, h⟩) : Quotient s ⊕ ℕ) else Sum.inr a) a =
    (fun a : ℕ => if h : a < n then (Sum.inl (Quotient.mk s ⟨a, h⟩) : Quotient s ⊕ ℕ) else Sum.inr a) b ↔ _
  simp only [a.2, b.2, dite_true, Sum.inl.injEq, Fin.eta]
  exact Quotient.eq

noncomputable def cfIdx {n : ℕ} (s : Setoid (Fin n)) (i : Fin n) : ℕ := blockIndex (cfExt s) i

noncomputable def cfk {n : ℕ} (s : Setoid (Fin n)) : ℕ := cfK (cfExt s) n

lemma cf_idx_lt {n : ℕ} (s : Setoid (Fin n)) (i : Fin n) : cfIdx s i < cfk s := cf_bi_lt _ _ _ i.2

lemma cf_idx_iff {n : ℕ} (s : Setoid (Fin n)) (i j : Fin n) : cfIdx s i = cfIdx s j ↔ s i j := by
  rw [cfIdx, cfIdx, cf_bi_iff, cf_ext_rel]

lemma cf_idx_surj {n : ℕ} (s : Setoid (Fin n)) (c : ℕ) (hc : c < cfk s) : ∃ i : Fin n, cfIdx s i = c := by
  obtain ⟨i, hi, h⟩ := cf_bi_surj _ n c hc
  exact ⟨⟨i, hi⟩, h⟩

lemma cf_bi_of_restrict {n : ℕ} (π : Setoid ℕ) (s : Setoid (Fin n)) (h : restrict n π = s) (i : Fin n) :
    blockIndex π i = cfIdx s i := by
  apply cf_bi_local π (cfExt s) n _ i i.2
  intro a b ha hb
  have := cf_ext_rel s ⟨a, ha⟩ ⟨b, hb⟩
  rw [this, ← h]; rfl



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



/-! ### measurability of coag / frag -/

abbrev PI := LambdaCoalescent.Rates.PInf

lemma cf_measurable_of {X : Type*} [MeasurableSpace X] (f : X → PI)
    (h : ∀ i j : ℕ, MeasurableSet {x | (f x).r i j}) : Measurable f := by
  apply Measurable.of_comap_le
  show MeasurableSpace.comap f (MeasurableSpace.comap _ inferInstance) ≤ _
  rw [MeasurableSpace.comap_comp, ← measurable_iff_comap_le, measurable_pi_iff]
  intro p
  exact measurableSet_setOfPred.1 (h p.1 p.2)

lemma cf_measurable_bi (i : ℕ) : Measurable (fun π : PI => blockIndex π i) := by
  have : (fun π : PI => blockIndex π i) =
      (fun s : Setoid (Fin (i+1)) => cfIdx s ⟨i, by omega⟩) ∘ (fun π : PI => restrict (i+1) π) := by
    funext π; exact cf_bi_of_restrict π _ rfl ⟨i, by omega⟩
  rw [this]; exact Measurable.comp (Measurable.of_discrete) (cf_measurable_restrict _)

lemma cf_ms_bi_eq {Y : Type*} [MeasurableSpace Y] (i a : ℕ) : MeasurableSet {x : PI × Y | blockIndex x.1 i = a} :=
  ((cf_measurable_bi i).comp measurable_fst) (measurableSet_singleton a)

lemma cf_measurable_coag : Measurable (β := PI) (fun x : PI × PI => coag x.1 x.2) := by
  apply cf_measurable_of
  intro i j
  have : {x : PI × PI | (coag x.1 x.2).r i j} =
      ⋃ a : ℕ, ⋃ b : ℕ, ({x : PI × PI | blockIndex x.1 i = a} ∩ {x | blockIndex x.1 j = b} ∩ {x | x.2.r a b}) := by
    ext x; simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h; exact ⟨_, _, ⟨rfl, rfl⟩, h⟩
    · rintro ⟨a, b, ⟨rfl, rfl⟩, h⟩; exact h
  rw [this]
  refine MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun b => ?_
  exact ((cf_ms_bi_eq i a).inter (cf_ms_bi_eq j b)).inter (measurable_snd (cf_meas_rel a b))

lemma cf_frag_rel (π' : Setoid ℕ) (Γ : ℕ → Setoid ℕ) (i j : ℕ) :
    (frag π' Γ).r i j ↔ blockIndex π' i = blockIndex π' j ∧ (Γ (blockIndex π' i)).r i j := by
  show (blockIndex π' i, {x | Γ (blockIndex π' i) i x}) = (blockIndex π' j, {x | Γ (blockIndex π' j) j x}) ↔ _
  rw [Prod.mk.injEq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have : j ∈ {x | Γ (blockIndex π' j) j x} := (Γ _).refl j
    rw [← h2] at this; exact this
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [← h1]; ext x; simp only [Set.mem_setOf_eq]
    exact ⟨fun h => (Γ _).trans ((Γ _).symm h2) h, fun h => (Γ _).trans h2 h⟩

lemma cf_measurable_frag : Measurable (β := PI) (fun y : PI × (ℕ → PI) => frag y.1 y.2) := by
  apply cf_measurable_of
  intro i j
  have : {y : PI × (ℕ → PI) | (frag y.1 y.2).r i j} =
      ⋃ m : ℕ, ({y : PI × (ℕ → PI) | blockIndex y.1 i = m} ∩ {y | blockIndex y.1 j = m} ∩ {y | (y.2 m).r i j}) := by
    ext y; simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    refine (cf_frag_rel y.1 y.2 i j).trans ?_
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨_, ⟨rfl, h1.symm⟩, h2⟩
    · rintro ⟨m, ⟨rfl, h1⟩, h2⟩; exact ⟨h1.symm, h2⟩
  rw [this]
  refine MeasurableSet.iUnion fun m => ?_
  have hm : Measurable (fun y : PI × (ℕ → PI) => y.2 m) := (measurable_pi_apply m).comp measurable_snd
  exact ((cf_ms_bi_eq i m).inter (cf_ms_bi_eq j m)).inter (hm (cf_meas_rel i j))

lemma cf_meas_cyl (n : ℕ) (s t : Setoid (Fin n)) : MeasurableSet {z : PI × PI | restrict n z.1 = s ∧ restrict n z.2 = t} := by
  have : {z : PI × PI | restrict n z.1 = s ∧ restrict n z.2 = t} = cyl2 n ⁻¹' {(s, t)} := by
    ext z; simp [cyl2]
  rw [this]; exact cf_measurable_cyl2 n (measurableSet_singleton _)

/-! ### finite combinatorics for coag -/

lemma cf_card_image_ker {X Y Z : Type*} [DecidableEq Y] [DecidableEq Z] (B : Finset X) (g : X → Y) (h : X → Z)
    (hk : ∀ i ∈ B, ∀ j ∈ B, g i = g j ↔ h i = h j) : (B.image g).card = (B.image h).card := by
  induction B using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have ih' := ih (fun i hi j hj => hk i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))
    rw [Finset.image_insert, Finset.image_insert]
    by_cases hg : g a ∈ s.image g
    · have hh : h a ∈ s.image h := by
        obtain ⟨j, hj, hja⟩ := Finset.mem_image.1 hg
        exact Finset.mem_image.2 ⟨j, hj, ((hk j (Finset.mem_insert_of_mem hj) a (Finset.mem_insert_self a s)).1 hja)⟩
      rw [Finset.insert_eq_of_mem hg, Finset.insert_eq_of_mem hh, ih']
    · have hh : h a ∉ s.image h := by
        intro hh; apply hg
        obtain ⟨j, hj, hja⟩ := Finset.mem_image.1 hh
        exact Finset.mem_image.2 ⟨j, hj, ((hk j (Finset.mem_insert_of_mem hj) a (Finset.mem_insert_self a s)).2 hja)⟩
      rw [Finset.card_insert_of_notMem hg, Finset.card_insert_of_notMem hh, ih']

noncomputable def cfRep {n : ℕ} (s : Setoid (Fin n)) (a : Fin (cfk s)) : Fin n :=
  Classical.choose (cf_idx_surj s a a.2)

lemma cf_rep_spec {n : ℕ} (s : Setoid (Fin n)) (a : Fin (cfk s)) : cfIdx s (cfRep s a) = a :=
  Classical.choose_spec (cf_idx_surj s a a.2)

noncomputable def cfSig {n : ℕ} (π₁ π₂ : Setoid (Fin n)) : Setoid (Fin (cfk π₁)) := π₂.comap (cfRep π₁)

noncomputable def cff {n : ℕ} (s : Setoid (Fin n)) (i : Fin n) : Fin (cfk s) := ⟨cfIdx s i, cf_idx_lt s i⟩

lemma cf_f_rep {n : ℕ} (s : Setoid (Fin n)) (a : Fin (cfk s)) : cff s (cfRep s a) = a := Fin.ext (cf_rep_spec s a)

lemma cf_f_iff {n : ℕ} (s : Setoid (Fin n)) (i j : Fin n) : cff s i = cff s j ↔ s i j := by
  rw [← cf_idx_iff, cff, cff, Fin.mk.injEq]

lemma cf_coag_set {n : ℕ} (π₁ π₂ : Setoid (Fin n)) (h : π₁ ≤ π₂) :
    {x : PI × PI | restrict n x.1 = π₁ ∧ restrict n (coag x.1 x.2) = π₂} =
      {π : PI | restrict n π = π₁} ×ˢ {γ : PI | restrict (cfk π₁) γ = cfSig π₁ π₂} := by
  ext ⟨x1, γ⟩
  simp only [Set.mem_setOf_eq, Set.mem_prod]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [cf_restrict_eq_iff] at h2
    apply (cf_restrict_eq_iff _ _ _).2
    intro a b
    have := h2 (cfRep π₁ a) (cfRep π₁ b)
    show γ.r a b ↔ π₂ (cfRep π₁ a) (cfRep π₁ b)
    rw [← this]
    show γ.r a b ↔ γ.r (blockIndex x1 (cfRep π₁ a)) (blockIndex x1 (cfRep π₁ b))
    rw [cf_bi_of_restrict x1 π₁ h1, cf_bi_of_restrict x1 π₁ h1, cf_rep_spec, cf_rep_spec]
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have h2 := (cf_restrict_eq_iff _ _ _).1 h2
    rw [cf_restrict_eq_iff]
    intro i j
    show γ.r (blockIndex x1 i) (blockIndex x1 j) ↔ π₂ i j
    rw [cf_bi_of_restrict x1 π₁ h1, cf_bi_of_restrict x1 π₁ h1]
    have := h2 (cff π₁ i) (cff π₁ j)
    have e1 : (((cff π₁ i) : Fin (cfk π₁)) : ℕ) = cfIdx π₁ i := rfl
    have e2 : (((cff π₁ j) : Fin (cfk π₁)) : ℕ) = cfIdx π₁ j := rfl
    rw [e1, e2] at this
    rw [this]
    have hi : π₁ (cfRep π₁ (cff π₁ i)) i := (cf_f_iff π₁ _ _).1 (cf_f_rep _ _)
    have hj : π₁ (cfRep π₁ (cff π₁ j)) j := (cf_f_iff π₁ _ _).1 (cf_f_rep _ _)
    show π₂ (cfRep π₁ (cff π₁ i)) (cfRep π₁ (cff π₁ j)) ↔ π₂ i j
    constructor
    · intro hh; exact π₂.trans (π₂.symm (cf_le h hi)) (π₂.trans hh (cf_le h hj))
    · intro hh; exact π₂.trans (cf_le h hi) (π₂.trans hh (π₂.symm (cf_le h hj)))

lemma cf_cls_sig {n : ℕ} (π₁ π₂ : Setoid (Fin n)) (h : π₁ ≤ π₂) (a : Fin (cfk π₁)) :
    cls (cfSig π₁ π₂) a = (cls π₂ (cfRep π₁ a)).image (cff π₁) := by
  ext c
  rw [cf_mem_cls, Finset.mem_image]
  constructor
  · intro hc; exact ⟨cfRep π₁ c, (cf_mem_cls _ _ _).2 hc, cf_f_rep _ _⟩
  · rintro ⟨j, hj, rfl⟩
    rw [cf_mem_cls] at hj
    show π₂ (cfRep π₁ a) (cfRep π₁ (cff π₁ j))
    have : π₁ j (cfRep π₁ (cff π₁ j)) := (cf_f_iff π₁ _ _).1 (cf_f_rep _ _).symm
    exact π₂.trans hj (cf_le h this)

lemma cf_bs_sig {n : ℕ} (π₁ π₂ : Setoid (Fin n)) (h : π₁ ≤ π₂) :
    blockSizes (cfSig π₁ π₂) = coagCounts π₁ π₂ := by
  have hb : blocks (cfSig π₁ π₂) = (blocks π₂).image (fun B => B.image (cff π₁)) := by
    ext C
    rw [cf_mem_blocks, Finset.mem_image]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨cls π₂ (cfRep π₁ a), (cf_mem_blocks _ _).2 ⟨_, rfl⟩, (cf_cls_sig π₁ π₂ h a).symm⟩
    · rintro ⟨B, hB, rfl⟩
      obtain ⟨i, rfl⟩ := (cf_mem_blocks _ _).1 hB
      refine ⟨cff π₁ i, ?_⟩
      rw [cf_cls_sig π₁ π₂ h]
      congr 1
      rw [cf_cls_eq]
      exact cf_le h ((cf_f_iff π₁ _ _).1 (cf_f_rep _ _))
  have hinj : Set.InjOn (fun B => B.image (cff π₁)) (blocks π₂ : Set (Finset (Fin n))) := by
    intro B hB B' hB' hBB
    simp only [Finset.mem_coe, cf_mem_blocks] at hB hB'
    obtain ⟨i, rfl⟩ := hB; obtain ⟨i', rfl⟩ := hB'
    have : cff π₁ i ∈ (cls π₂ i').image (cff π₁) := by
      simp only at hBB; rw [← hBB]; exact Finset.mem_image_of_mem _ ((cf_mem_cls _ _ _).2 (π₂.refl i))
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.1 this
    rw [cf_f_iff] at hji
    rw [cf_mem_cls] at hj
    rw [cf_cls_eq]; exact π₂.symm (π₂.trans hj (cf_le h hji))
  rw [blockSizes, hb, Finset.image_val_of_injOn hinj, Multiset.map_map, coagCounts]
  apply Multiset.map_congr rfl
  intro B hB
  obtain ⟨i, rfl⟩ := (cf_mem_blocks _ _).1 (by simpa using hB)
  simp only [Function.comp_apply]
  rw [cf_filt π₁ π₂ h i]
  apply cf_card_image_ker
  intro a _ b _
  rw [cf_f_iff, cf_cls_eq]

lemma cf_coag_mono (x1 γ : Setoid ℕ) (n : ℕ) : restrict n x1 ≤ restrict n (coag x1 γ) := by
  rw [Setoid.le_def]
  intro i j hij
  show γ.r (blockIndex x1 i) (blockIndex x1 j)
  rw [cf_bi_eq x1 i j hij]

lemma cf_frag_mono (y1 : Setoid ℕ) (Γ : ℕ → Setoid ℕ) (n : ℕ) : restrict n (frag y1 Γ) ≤ restrict n y1 := by
  rw [Setoid.le_def]
  intro i j hij
  exact cf_bi_inj y1 i j ((cf_frag_rel y1 Γ i j).1 hij).1

lemma cf_real_prod {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y)
    [SFinite ν] (A : Set X) (B : Set Y) : (μ.prod ν).real (A ×ˢ B) = μ.real A * ν.real B := by
  rw [measureReal_def, Measure.prod_prod, ENNReal.toReal_mul]; rfl

lemma cf_coag_real (μ₁ ν : Measure PI) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure ν]
    (p₁ p : Multiset ℕ → ℝ) (hμ₁ : IsEPFLaw p₁ μ₁) (hν : IsEPFLaw p ν) (n : ℕ) (π₁ π₂ : Setoid (Fin n))
    (h : π₁ ≤ π₂) :
    (μ₁.prod ν).real {x : PI × PI | restrict n x.1 = π₁ ∧ restrict n (coag x.1 x.2) = π₂} =
      p₁ (blockSizes π₁) * p (coagCounts π₁ π₂) := by
  rw [cf_coag_set π₁ π₂ h, cf_real_prod, hμ₁, hν, cf_bs_sig π₁ π₂ h]



/-! ### exchangeability -/

lemma cf_GL {b n : ℕ} (g : Fin b → Fin n) (hg : Function.Injective g) (s : Setoid (Fin n)) :
    blockSizes (s.comap g) =
      (((Finset.univ.image g).image (fun i => (Finset.univ.image g).filter (fun j => s i j))).val.map Finset.card) := by
  let gE : Fin b ↪ Fin n := ⟨g, hg⟩
  have h1 : (Finset.univ.image g).image (fun i => (Finset.univ.image g).filter (fun j => s i j)) =
      (blocks (s.comap g)).image (Finset.map gE) := by
    rw [cf_blocks_eq, Finset.image_image, Finset.image_image]
    apply Finset.image_congr
    intro a _
    simp only [Function.comp_apply]
    ext x
    simp only [cls, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_map]
    constructor
    · rintro ⟨⟨c, rfl⟩, hc⟩; exact ⟨c, hc, rfl⟩
    · rintro ⟨c, hc, rfl⟩; exact ⟨⟨c, rfl⟩, hc⟩
  rw [h1, Finset.image_val_of_injOn (fun A _ B _ h => Finset.map_injective gE h), Multiset.map_map, blockSizes]
  congr 1; funext A; simp

lemma cf_bs_comap_equiv {n : ℕ} (e : Fin n ≃ Fin n) (s : Setoid (Fin n)) :
    blockSizes (s.comap e) = blockSizes s := by
  rw [cf_GL e e.injective]
  have : Finset.univ.image e = Finset.univ := by
    ext x; simp only [Finset.mem_image, Finset.mem_univ, true_and, iff_true]; exact ⟨e.symm x, by simp⟩
  rw [this]
  rfl

lemma cf_real_restrict_preimage (κ : Measure PI) [IsProbabilityMeasure κ] (p : Multiset ℕ → ℝ)
    (hκ : IsEPFLaw p κ) (n : ℕ) (T : Finset (Setoid (Fin n))) :
    κ.real ((fun γ : PI => restrict n γ) ⁻¹' (T : Set (Setoid (Fin n)))) = ∑ τ ∈ T, p (blockSizes τ) := by
  rw [← sum_measureReal_preimage_singleton T (fun y _ => cf_measurable_restrict n (measurableSet_singleton y))]
  apply Finset.sum_congr rfl
  intro τ _
  exact hκ n τ

lemma cf_exch (κ : Measure PI) [IsProbabilityMeasure κ] (p : Multiset ℕ → ℝ) (hκ : IsEPFLaw p κ)
    (n : ℕ) (B : Finset (Fin n)) (s : Setoid (Fin n)) :
    κ.real {γ : PI | ∀ i ∈ B, ∀ l ∈ B, (γ.r i l ↔ s i l)} =
      p ((B.image (fun i => B.filter (fun j => s i j))).val.map Finset.card) := by
  set b := B.card with hb
  have hbn : b ≤ n := by
    have := Finset.card_le_univ B; simpa using this
  let g : Fin b → Fin n := fun c => (B.equivFin.symm c).val
  have hg : Function.Injective g := fun c d h => B.equivFin.symm.injective (Subtype.ext h)
  have hgB : Finset.univ.image g = B := by
    ext x; simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨c, rfl⟩; exact (B.equivFin.symm c).2
    · intro hx; exact ⟨B.equivFin ⟨x, hx⟩, by simp [g]⟩
  obtain ⟨e, he⟩ := Equiv.Perm.exists_extending_pair (Fin.castLE hbn) g (Fin.castLE_injective hbn) hg
  let s' : Setoid (Fin b) := s.comap g
  have hs' : blockSizes s' = (B.image (fun i => B.filter (fun j => s i j))).val.map Finset.card := by
    rw [cf_GL g hg, hgB]
  rw [← hs', ← hκ b s']
  let T1 : Finset (Setoid (Fin n)) := Finset.univ.filter (fun τ => ∀ i ∈ B, ∀ l ∈ B, (τ i l ↔ s i l))
  let T2 : Finset (Setoid (Fin n)) := Finset.univ.filter (fun τ => τ.comap (Fin.castLE hbn) = s')
  have e1 : {γ : PI | ∀ i ∈ B, ∀ l ∈ B, (γ.r i l ↔ s i l)} =
      (fun γ : PI => restrict n γ) ⁻¹' (T1 : Set (Setoid (Fin n))) := by
    ext γ; simp only [T1, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_preimage, Set.mem_setOf_eq]; rfl
  have e2 : {γ : PI | restrict b γ = s'} = (fun γ : PI => restrict n γ) ⁻¹' (T2 : Set (Setoid (Fin n))) := by
    ext γ; simp only [T2, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_preimage, Set.mem_setOf_eq]; rfl
  rw [e1, e2, cf_real_restrict_preimage κ p hκ, cf_real_restrict_preimage κ p hκ]
  let E : Setoid (Fin n) ≃ Setoid (Fin n) :=
    { toFun := fun τ => τ.comap e
      invFun := fun τ => τ.comap e.symm
      left_inv := fun τ => by apply Setoid.ext; intro a c; simp [Setoid.comap_rel]
      right_inv := fun τ => by apply Setoid.ext; intro a c; simp [Setoid.comap_rel] }
  apply Finset.sum_equiv E
  · intro τ
    simp only [T1, T2, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hτ
      apply Setoid.ext; intro a c
      show τ (e (Fin.castLE hbn a)) (e (Fin.castLE hbn c)) ↔ s (g a) (g c)
      rw [he, he]
      apply hτ
      · rw [← hgB]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
      · rw [← hgB]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    · intro hτ i hi l hl
      rw [← hgB] at hi hl
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hi
      obtain ⟨c, _, rfl⟩ := Finset.mem_image.1 hl
      have := congrArg (fun σ : Setoid (Fin b) => σ a c) hτ
      simp only [eq_iff_iff] at this
      have h' : (E τ).comap (Fin.castLE hbn) a c ↔ τ (g a) (g c) := by
        show τ (e (Fin.castLE hbn a)) (e (Fin.castLE hbn c)) ↔ _
        rw [he, he]
      rw [← h', this]; rfl
  · intro τ _
    show p (blockSizes τ) = p (blockSizes (τ.comap e))
    rw [cf_bs_comap_equiv]



/-! ### frag cylinder -/

noncomputable def cfA {n : ℕ} (π₁ π₂ : Setoid (Fin n)) (m : ℕ) : Set PI :=
  {γ : PI | ∀ i l : Fin n, cfIdx π₂ i = m → cfIdx π₂ l = m → (γ.r i l ↔ π₁ i l)}

lemma cf_meas_A {n : ℕ} (π₁ π₂ : Setoid (Fin n)) (m : ℕ) : MeasurableSet (cfA π₁ π₂ m) := by
  have : cfA π₁ π₂ m = (fun γ : PI => restrict n γ) ⁻¹'
      {τ | ∀ i l : Fin n, cfIdx π₂ i = m → cfIdx π₂ l = m → (τ i l ↔ π₁ i l)} := rfl
  rw [this]; exact cf_measurable_restrict n (MeasurableSet.of_discrete)

lemma cf_frag_set {n : ℕ} (π₁ π₂ : Setoid (Fin n)) (h : π₁ ≤ π₂) :
    {y : PI × (ℕ → PI) | restrict n (frag y.1 y.2) = π₁ ∧ restrict n y.1 = π₂} =
      {π : PI | restrict n π = π₂} ×ˢ Set.pi (↑(Finset.range (cfk π₂))) (cfA π₁ π₂) := by
  ext ⟨y1, Γ⟩
  simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_pi, Finset.coe_range, Set.mem_Iio]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h2, ?_⟩
    intro m _ i l hi hl
    have h3 := (cf_frag_rel y1 Γ i l).symm.trans ((cf_restrict_eq_iff _ _ _).1 h1 i l)
    have b1 := cf_bi_of_restrict y1 π₂ h2 i
    have b2 := cf_bi_of_restrict y1 π₂ h2 l
    rw [b1, b2, hi, hl] at h3
    simpa using h3
  · rintro ⟨h2, hA⟩
    refine ⟨?_, h2⟩
    apply (cf_restrict_eq_iff _ _ _).2
    intro i l
    refine (cf_frag_rel y1 Γ i l).trans ?_
    rw [cf_bi_of_restrict y1 π₂ h2, cf_bi_of_restrict y1 π₂ h2]
    by_cases hil : cfIdx π₂ i = cfIdx π₂ l
    · have := hA (cfIdx π₂ i) (cf_idx_lt π₂ i) i l rfl hil.symm
      exact ⟨fun hh => this.1 hh.2, fun hh => ⟨hil, this.2 hh⟩⟩
    · have : ¬ π₁ i l := fun h' => hil ((cf_idx_iff π₂ i l).2 (cf_le h h'))
      exact ⟨fun hh => absurd hh.1 hil, fun hh => absurd hh this⟩

noncomputable def cfBm {n : ℕ} (s : Setoid (Fin n)) (m : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => cfIdx s i = m)

lemma cf_Bm_cls {n : ℕ} (s : Setoid (Fin n)) (i : Fin n) : cfBm s (cfIdx s i) = cls s i := by
  ext j
  simp only [cfBm, cls, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [cf_idx_iff]; exact ⟨fun h => s.symm h, fun h => s.symm h⟩

lemma cf_blocks_Bm {n : ℕ} (s : Setoid (Fin n)) :
    blocks s = (Finset.range (cfk s)).image (cfBm s) := by
  ext B
  rw [cf_mem_blocks, Finset.mem_image]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨cfIdx s i, Finset.mem_range.2 (cf_idx_lt s i), cf_Bm_cls s i⟩
  · rintro ⟨m, hm, rfl⟩
    obtain ⟨i, rfl⟩ := cf_idx_surj s m (Finset.mem_range.1 hm)
    exact ⟨i, (cf_Bm_cls s i).symm⟩

lemma cf_Bm_inj {n : ℕ} (s : Setoid (Fin n)) : Set.InjOn (cfBm s) (Finset.range (cfk s) : Set ℕ) := by
  intro m hm m' hm' hmm
  simp only [Finset.coe_range, Set.mem_Iio] at hm hm'
  obtain ⟨i, rfl⟩ := cf_idx_surj s m hm
  have : i ∈ cfBm s m' := by
    rw [← hmm]; simp [cfBm]
  simpa [cfBm] using this

lemma cf_A_real (κ : Measure PI) [IsProbabilityMeasure κ] (p : Multiset ℕ → ℝ) (hκ : IsEPFLaw p κ)
    {n : ℕ} (π₁ π₂ : Setoid (Fin n)) (h : π₁ ≤ π₂) (i : Fin n) :
    κ.real (cfA π₁ π₂ (cfIdx π₂ i)) =
      p (((blocks π₁).filter (fun A => A ⊆ cls π₂ i)).val.map Finset.card) := by
  have e : cfA π₁ π₂ (cfIdx π₂ i) = {γ : PI | ∀ j ∈ cls π₂ i, ∀ l ∈ cls π₂ i, (γ.r j l ↔ π₁ j l)} := by
    ext γ
    simp only [cfA, Set.mem_setOf_eq, ← cf_Bm_cls]
    simp only [cfBm, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro H j hj l hl; exact H j l hj hl
    · intro H j l hj hl; exact H j hj l hl
  have hi : (cls π₂ i).image (fun j => (cls π₂ i).filter (fun l => π₁ j l)) = (cls π₂ i).image (cls π₁) := by
    apply Finset.image_congr
    intro j hj
    simp only [Finset.mem_coe, cf_mem_cls] at hj
    ext l
    simp only [Finset.mem_filter, cf_mem_cls]
    exact ⟨fun hh => hh.2, fun hh => ⟨π₂.trans hj (cf_le h hh), hh⟩⟩
  rw [e, cf_exch κ p hκ, cf_filt π₁ π₂ h i, hi]

lemma cf_frag_real (ρ κ : Measure PI) [IsProbabilityMeasure ρ] [IsProbabilityMeasure κ]
    (p₂ phat : Multiset ℕ → ℝ) (hρ : IsEPFLaw p₂ ρ) (hκ : IsEPFLaw phat κ) (n : ℕ)
    (π₁ π₂ : Setoid (Fin n)) (h : π₁ ≤ π₂) :
    (ρ.prod (Measure.infinitePi (fun _ : ℕ => κ))).real
        {y : PI × (ℕ → PI) | restrict n (frag y.1 y.2) = π₁ ∧ restrict n y.1 = π₂} =
      ((fragSizes π₁ π₂).map phat).prod * p₂ (blockSizes π₂) := by
  rw [cf_frag_set π₁ π₂ h, cf_real_prod, hρ, mul_comm]
  congr 1
  rw [measureReal_def, Measure.infinitePi_pi (μ := fun _ : ℕ => κ) (mt := fun m _ => cf_meas_A π₁ π₂ m), ENNReal.toReal_prod]
  rw [fragSizes, Multiset.map_map, ← Finset.prod_eq_multiset_prod, cf_blocks_Bm π₂,
    Finset.prod_image (cf_Bm_inj π₂)]
  apply Finset.prod_congr rfl
  intro m hm
  obtain ⟨i, rfl⟩ := cf_idx_surj π₂ m (Finset.mem_range.1 hm)
  rw [← measureReal_def, cf_A_real κ phat hκ π₁ π₂ h i, Function.comp_apply, cf_Bm_cls]

/-! ### Theorem 12 -/

lemma cf_coag_map (μ ν : Measure PI) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (n : ℕ)
    (s t : Setoid (Fin n)) :
    ((μ.prod ν).map (fun x : PI × PI => ((x.1, coag x.1 x.2) : PI × PI)))
        {z : PI × PI | restrict n z.1 = s ∧ restrict n z.2 = t} =
      (μ.prod ν) {x : PI × PI | restrict n x.1 = s ∧ restrict n (coag x.1 x.2) = t} := by
  rw [Measure.map_apply (measurable_fst.prodMk cf_measurable_coag) (cf_meas_cyl n s t)]
  rfl

lemma cf_frag_map (ρ κ : Measure PI) [IsProbabilityMeasure ρ] [IsProbabilityMeasure κ] (n : ℕ)
    (s t : Setoid (Fin n)) :
    ((ρ.prod (Measure.infinitePi (fun _ : ℕ => κ))).map
        (fun y : PI × (ℕ → PI) => ((frag y.1 y.2, y.1) : PI × PI)))
        {z : PI × PI | restrict n z.1 = s ∧ restrict n z.2 = t} =
      (ρ.prod (Measure.infinitePi (fun _ : ℕ => κ)))
        {y : PI × (ℕ → PI) | restrict n (frag y.1 y.2) = s ∧ restrict n y.1 = t} := by
  rw [Measure.map_apply (cf_measurable_frag.prodMk measurable_fst) (cf_meas_cyl n s t)]
  rfl

lemma cf_coag_empty {n : ℕ} (s t : Setoid (Fin n)) (hst : ¬ s ≤ t) :
    {x : PI × PI | restrict n x.1 = s ∧ restrict n (coag x.1 x.2) = t} = ∅ := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨h1, h2⟩
  exact hst (h1 ▸ h2 ▸ cf_coag_mono x.1 x.2 n)

lemma cf_frag_empty {n : ℕ} (s t : Setoid (Fin n)) (hst : ¬ s ≤ t) :
    {y : PI × (ℕ → PI) | restrict n (frag y.1 y.2) = s ∧ restrict n y.1 = t} = ∅ := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨h1, h2⟩
  exact hst (h1 ▸ h2 ▸ cf_frag_mono y.1 y.2 n)

theorem theorem_12_core (α β θ : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hθ : -(α * β) < θ)
    (μ ν ρ κ : Measure LambdaCoalescent.Rates.PInf) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure κ]
    (hμ : IsEPFLaw (pdEPF α θ) μ) (hν : IsEPFLaw (pdEPF β (θ / α)) ν)
    (hρ : IsEPFLaw (pdEPF (α * β) θ) ρ) (hκ : IsEPFLaw (pdEPF α (-(α * β))) κ) :
    ∀ S : Set (LambdaCoalescent.Rates.PInf × LambdaCoalescent.Rates.PInf), MeasurableSet S →
      (μ.prod ν) {x | (x.1, coag x.1 x.2) ∈ S} =
        (ρ.prod (Measure.infinitePi (fun _ : ℕ => κ))) {y | (frag y.1 y.2, y.1) ∈ S} := by
  intro S hS
  have hF : Measurable (fun x : PI × PI => ((x.1, coag x.1 x.2) : PI × PI)) :=
    measurable_fst.prodMk cf_measurable_coag
  have hG : Measurable (fun y : PI × (ℕ → PI) => ((frag y.1 y.2, y.1) : PI × PI)) :=
    cf_measurable_frag.prodMk measurable_fst
  have hmaps : (μ.prod ν).map (fun x : PI × PI => ((x.1, coag x.1 x.2) : PI × PI)) =
      (ρ.prod (Measure.infinitePi (fun _ : ℕ => κ))).map
        (fun y : PI × (ℕ → PI) => ((frag y.1 y.2, y.1) : PI × PI)) := by
    apply cf_uniq
    intro n s t
    rw [cf_coag_map, cf_frag_map]
    by_cases hst : s ≤ t
    · rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)]
      show (μ.prod ν).real _ = (ρ.prod (Measure.infinitePi (fun _ : ℕ => κ))).real _
      rw [cf_coag_real μ ν _ _ hμ hν n s t hst, cf_frag_real ρ κ _ _ hρ hκ n s t hst]
      exact epf_identity_core α β θ hα0 hα1 hβ0 hβ1 hθ n s t hst
    · rw [cf_coag_empty s t hst, cf_frag_empty s t hst, measure_empty, measure_empty]
  calc (μ.prod ν) {x | (x.1, coag x.1 x.2) ∈ S}
      = ((μ.prod ν).map (fun x : PI × PI => ((x.1, coag x.1 x.2) : PI × PI))) S :=
        (Measure.map_apply hF hS).symm
    _ = ((ρ.prod (Measure.infinitePi (fun _ : ℕ => κ))).map
        (fun y : PI × (ℕ → PI) => ((frag y.1 y.2, y.1) : PI × PI))) S := by rw [hmaps]
    _ = _ := Measure.map_apply hG hS



/-! ### converse directions (Lemmas 34, 35) -/

lemma cf_cyl_pre (n : ℕ) (s t : Setoid (Fin n)) :
    cyl2 n ⁻¹' {(s, t)} = {z : PI × PI | restrict n z.1 = s ∧ restrict n z.2 = t} := by
  ext z; simp [cyl2]

lemma cf_rev (M Q : Measure (PI × PI)) [IsProbabilityMeasure M] [IsProbabilityMeasure Q]
    (hQ0 : ∀ n (s t : Setoid (Fin n)), ¬ s ≤ t → Q {z : PI × PI | restrict n z.1 = s ∧ restrict n z.2 = t} = 0)
    (hMQ : ∀ n (s t : Setoid (Fin n)), s ≤ t → M {z : PI × PI | restrict n z.1 = s ∧ restrict n z.2 = t} =
      Q {z : PI × PI | restrict n z.1 = s ∧ restrict n z.2 = t}) : M = Q := by
  apply cf_uniq
  intro n s t
  by_cases hst : s ≤ t
  · exact hMQ n s t hst
  rw [hQ0 n s t hst]
  have hsum : ∀ R : Measure (PI × PI), IsProbabilityMeasure R →
      ∑ st : Setoid (Fin n) × Setoid (Fin n), R (cyl2 n ⁻¹' {st}) = 1 := by
    intro R _
    rw [sum_measure_preimage_singleton _ (fun y _ => cf_measurable_cyl2 n (measurableSet_singleton y))]
    simp
  have hsM := hsum M inferInstance
  have hsQ := hsum Q inferInstance
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun st : Setoid (Fin n) × Setoid (Fin n) => st.1 ≤ st.2)]
    at hsM hsQ
  have eq_on : ∀ st ∈ Finset.univ.filter (fun st : Setoid (Fin n) × Setoid (Fin n) => st.1 ≤ st.2),
      M (cyl2 n ⁻¹' {st}) = Q (cyl2 n ⁻¹' {st}) := by
    rintro ⟨a, b⟩ hab
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hab
    rw [cf_cyl_pre]; exact hMQ n a b hab
  have Q_off : ∀ st ∈ Finset.univ.filter (fun st : Setoid (Fin n) × Setoid (Fin n) => ¬ st.1 ≤ st.2),
      Q (cyl2 n ⁻¹' {st}) = 0 := by
    rintro ⟨a, b⟩ hab
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hab
    rw [cf_cyl_pre]; exact hQ0 n a b hab
  rw [Finset.sum_congr rfl eq_on] at hsM
  rw [Finset.sum_eq_zero Q_off, add_zero] at hsQ
  rw [hsQ] at hsM
  have hX := (ENNReal.add_right_inj ENNReal.one_ne_top).1 (hsM.trans (add_zero 1).symm)
  have := (Finset.sum_eq_zero_iff.1 hX) (s, t) (by simp [hst])
  rw [cf_cyl_pre] at this
  exact this

theorem lemma_34_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₁ X₂ : Ω → LambdaCoalescent.Rates.PInf) (hX₁ : Measurable X₁) (hX₂ : Measurable X₂)
    (p₁ p : Multiset ℕ → ℝ) (μ₁ ν : Measure LambdaCoalescent.Rates.PInf) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure ν]
    (hμ₁ : IsEPFLaw p₁ μ₁) (hν : IsEPFLaw p ν) :
    (P.map X₁ = μ₁ ∧
        ∀ S : Set (LambdaCoalescent.Rates.PInf × LambdaCoalescent.Rates.PInf), MeasurableSet S →
          P {ω | (X₁ ω, X₂ ω) ∈ S} = (μ₁.prod ν) {x | (x.1, coag x.1 x.2) ∈ S}) ↔
      ∀ (n : ℕ) (π₁ π₂ : Setoid (Fin n)), π₁ ≤ π₂ →
        P.real {ω | restrict n (X₁ ω) = π₁ ∧ restrict n (X₂ ω) = π₂} =
          p₁ (blockSizes π₁) * p (coagCounts π₁ π₂) := by
  have hX : Measurable (fun ω => ((X₁ ω, X₂ ω) : PI × PI)) := hX₁.prodMk hX₂
  have hF : Measurable (fun x : PI × PI => ((x.1, coag x.1 x.2) : PI × PI)) :=
    measurable_fst.prodMk cf_measurable_coag
  have hM : ∀ n (s t : Setoid (Fin n)), (P.map (fun ω => ((X₁ ω, X₂ ω) : PI × PI)))
      {z : PI × PI | restrict n z.1 = s ∧ restrict n z.2 = t} =
      P {ω | restrict n (X₁ ω) = s ∧ restrict n (X₂ ω) = t} := by
    intro n s t; rw [Measure.map_apply hX (cf_meas_cyl n s t)]; rfl
  constructor
  · rintro ⟨_, hS⟩ n π₁ π₂ h
    have := hS _ (cf_meas_cyl n π₁ π₂)
    rw [measureReal_def]
    change (P {ω | (X₁ ω, X₂ ω) ∈ {z : PI × PI | restrict n z.1 = π₁ ∧ restrict n z.2 = π₂}}).toReal = _
    rw [this]
    exact cf_coag_real μ₁ ν p₁ p hμ₁ hν n π₁ π₂ h
  · intro H
    have := Measure.isProbabilityMeasure_map (μ := P) hX.aemeasurable
    have := Measure.isProbabilityMeasure_map (μ := μ₁.prod ν) hF.aemeasurable
    have hMQ : P.map (fun ω => ((X₁ ω, X₂ ω) : PI × PI)) = (μ₁.prod ν).map
        (fun x : PI × PI => ((x.1, coag x.1 x.2) : PI × PI)) := by
      apply cf_rev
      · intro n s t hst; rw [cf_coag_map, cf_coag_empty s t hst, measure_empty]
      · intro n s t hst
        rw [hM, cf_coag_map, ← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)]
        exact (H n s t hst).trans (cf_coag_real μ₁ ν p₁ p hμ₁ hν n s t hst).symm
    refine ⟨?_, ?_⟩
    · have : P.map X₁ = (P.map (fun ω => ((X₁ ω, X₂ ω) : PI × PI))).map Prod.fst := by
        rw [Measure.map_map measurable_fst hX]; rfl
      rw [this, hMQ, Measure.map_map measurable_fst hF]
      show (μ₁.prod ν).map Prod.fst = μ₁
      rw [Measure.map_fst_prod, measure_univ, one_smul]
    · intro S hS
      calc P {ω | (X₁ ω, X₂ ω) ∈ S} = (P.map (fun ω => ((X₁ ω, X₂ ω) : PI × PI))) S :=
            (Measure.map_apply hX hS).symm
        _ = ((μ₁.prod ν).map (fun x : PI × PI => ((x.1, coag x.1 x.2) : PI × PI))) S := by rw [hMQ]
        _ = _ := Measure.map_apply hF hS

theorem lemma_35_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₁ X₂ : Ω → LambdaCoalescent.Rates.PInf) (hX₁ : Measurable X₁) (hX₂ : Measurable X₂)
    (p₂ phat : Multiset ℕ → ℝ) (μ₂ νhat : Measure LambdaCoalescent.Rates.PInf)
    [IsProbabilityMeasure μ₂] [IsProbabilityMeasure νhat]
    (hμ₂ : IsEPFLaw p₂ μ₂) (hνhat : IsEPFLaw phat νhat) :
    (P.map X₂ = μ₂ ∧
        ∀ S : Set (LambdaCoalescent.Rates.PInf × LambdaCoalescent.Rates.PInf), MeasurableSet S →
          P {ω | (X₁ ω, X₂ ω) ∈ S} =
            (μ₂.prod (Measure.infinitePi (fun _ : ℕ => νhat))) {y | (frag y.1 y.2, y.1) ∈ S}) ↔
      ∀ (n : ℕ) (π₁ π₂ : Setoid (Fin n)), π₁ ≤ π₂ →
        P.real {ω | restrict n (X₁ ω) = π₁ ∧ restrict n (X₂ ω) = π₂} =
          ((fragSizes π₁ π₂).map phat).prod * p₂ (blockSizes π₂) := by
  have hX : Measurable (fun ω => ((X₁ ω, X₂ ω) : PI × PI)) := hX₁.prodMk hX₂
  have hG : Measurable (fun y : PI × (ℕ → PI) => ((frag y.1 y.2, y.1) : PI × PI)) :=
    cf_measurable_frag.prodMk measurable_fst
  have hM : ∀ n (s t : Setoid (Fin n)), (P.map (fun ω => ((X₁ ω, X₂ ω) : PI × PI)))
      {z : PI × PI | restrict n z.1 = s ∧ restrict n z.2 = t} =
      P {ω | restrict n (X₁ ω) = s ∧ restrict n (X₂ ω) = t} := by
    intro n s t; rw [Measure.map_apply hX (cf_meas_cyl n s t)]; rfl
  constructor
  · rintro ⟨_, hS⟩ n π₁ π₂ h
    have := hS _ (cf_meas_cyl n π₁ π₂)
    rw [measureReal_def]
    change (P {ω | (X₁ ω, X₂ ω) ∈ {z : PI × PI | restrict n z.1 = π₁ ∧ restrict n z.2 = π₂}}).toReal = _
    rw [this]
    exact cf_frag_real μ₂ νhat p₂ phat hμ₂ hνhat n π₁ π₂ h
  · intro H
    have := Measure.isProbabilityMeasure_map (μ := P) hX.aemeasurable
    have := Measure.isProbabilityMeasure_map (μ := μ₂.prod (Measure.infinitePi (fun _ : ℕ => νhat))) hG.aemeasurable
    have hMQ : P.map (fun ω => ((X₁ ω, X₂ ω) : PI × PI)) =
        (μ₂.prod (Measure.infinitePi (fun _ : ℕ => νhat))).map
          (fun y : PI × (ℕ → PI) => ((frag y.1 y.2, y.1) : PI × PI)) := by
      apply cf_rev
      · intro n s t hst; rw [cf_frag_map, cf_frag_empty s t hst, measure_empty]
      · intro n s t hst
        rw [hM, cf_frag_map, ← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)]
        exact (H n s t hst).trans (cf_frag_real μ₂ νhat p₂ phat hμ₂ hνhat n s t hst).symm
    refine ⟨?_, ?_⟩
    · have : P.map X₂ = (P.map (fun ω => ((X₁ ω, X₂ ω) : PI × PI))).map Prod.snd := by
        rw [Measure.map_map measurable_snd hX]; rfl
      rw [this, hMQ, Measure.map_map measurable_snd hG]
      show (μ₂.prod (Measure.infinitePi (fun _ : ℕ => νhat))).map Prod.fst = μ₂
      rw [Measure.map_fst_prod, measure_univ, one_smul]
    · intro S hS
      calc P {ω | (X₁ ω, X₂ ω) ∈ S} = (P.map (fun ω => ((X₁ ω, X₂ ω) : PI × PI))) S :=
            (Measure.map_apply hX hS).symm
        _ = ((μ₂.prod (Measure.infinitePi (fun _ : ℕ => νhat))).map
          (fun y : PI × (ℕ → PI) => ((frag y.1 y.2, y.1) : PI × PI))) S := by rw [hMQ]
        _ = _ := Measure.map_apply hG hS



/-! ### Lemma 9: Chinese restaurant construction -/

noncomputable def cfExtd {n : ℕ} (s : Setoid (Fin n)) (c : ℕ) : Setoid (Fin (n+1)) :=
  Setoid.ker (fun i : Fin (n+1) => if h : i.val < n then cfIdx s ⟨i, h⟩ else c)

lemma cf_extd_rel_lt {n : ℕ} (s : Setoid (Fin n)) (c : ℕ) (i j : Fin (n+1)) (hi : i.val < n) (hj : j.val < n) :
    cfExtd s c i j ↔ s ⟨i, hi⟩ ⟨j, hj⟩ := by
  show (if h : i.val < n then cfIdx s ⟨i, h⟩ else c) = (if h : j.val < n then cfIdx s ⟨j, h⟩ else c) ↔ _
  rw [dif_pos hi, dif_pos hj, cf_idx_iff]

lemma cf_extd_rel_last {n : ℕ} (s : Setoid (Fin n)) (c : ℕ) (i : Fin (n+1)) (hi : i.val < n) :
    cfExtd s c i (Fin.last n) ↔ cfIdx s ⟨i, hi⟩ = c := by
  show (if h : i.val < n then cfIdx s ⟨i, h⟩ else c) = (if h : (Fin.last n).val < n then cfIdx s ⟨_, h⟩ else c) ↔ _
  rw [dif_pos hi, dif_neg (by simp)]

/-- restriction of a partition of `[n+1]` to `[n]` -/
def cfRes {n : ℕ} (s : Setoid (Fin (n+1))) : Setoid (Fin n) := s.comap (Fin.castLE (Nat.le_succ n))

lemma cf_res_extd {n : ℕ} (s : Setoid (Fin n)) (c : ℕ) : cfRes (cfExtd s c) = s := by
  apply Setoid.ext; intro i j
  exact cf_extd_rel_lt s c _ _ i.2 j.2

lemma cf_fin_cases {n : ℕ} (i : Fin (n+1)) : i.val < n ∨ i = Fin.last n := by
  rcases Nat.lt_or_ge i.val n with h | h
  · exact Or.inl h
  · right; ext; simp; omega

noncomputable def cfCstar {n : ℕ} (s' : Setoid (Fin (n+1))) : ℕ :=
  if h : ∃ i : Fin n, s' (Fin.castLE (Nat.le_succ n) i) (Fin.last n) then cfIdx (cfRes s') (Classical.choose h)
  else cfk (cfRes s')

lemma cf_cstar_le {n : ℕ} (s' : Setoid (Fin (n+1))) : cfCstar s' ≤ cfk (cfRes s') := by
  unfold cfCstar; split_ifs with h
  · exact (cf_idx_lt _ _).le
  · exact le_rfl

lemma cf_extd_iff {n : ℕ} (s' : Setoid (Fin (n+1))) (c : ℕ) (hc : c ≤ cfk (cfRes s')) :
    cfExtd (cfRes s') c = s' ↔ c = cfCstar s' := by
  set s := cfRes s' with hs
  have key : ∀ i : Fin n, (cfExtd s c (Fin.castLE (Nat.le_succ n) i) (Fin.last n) ↔ cfIdx s i = c) :=
    fun i => cf_extd_rel_last s c _ i.2
  constructor
  · intro he
    unfold cfCstar
    split_ifs with h
    · have h0 := Classical.choose_spec h
      generalize Classical.choose h = i0 at h0 ⊢
      rw [← he, key] at h0
      rw [← hs]; exact h0.symm
    · push_neg at h
      rw [← hs]
      rcases Nat.lt_or_ge c (cfk s) with hlt | hge
      · exfalso
        obtain ⟨i, hi⟩ := cf_idx_surj s c hlt
        apply h i; rw [← he, key]; exact hi
      · omega
  · intro hcs
    apply Setoid.ext
    intro i j
    have hres : ∀ a b : Fin (n+1), (ha : a.val < n) → (hb : b.val < n) →
        (s' a b ↔ s ⟨a, ha⟩ ⟨b, hb⟩) := by
      intro a b ha hb; rfl
    have hlast : ∀ a : Fin (n+1), (ha : a.val < n) → (s' a (Fin.last n) ↔ cfIdx s ⟨a, ha⟩ = c) := by
      intro a ha
      rw [hcs]; unfold cfCstar
      split_ifs with h
      · have h0 := Classical.choose_spec h
        generalize Classical.choose h = i0 at h0 ⊢
        rw [← hs]
        constructor
        · intro ha'
          rw [cf_idx_iff]
          have : s' a (Fin.castLE (Nat.le_succ n) i0) := s'.trans ha' (s'.symm h0)
          exact this
        · intro he
          rw [cf_idx_iff] at he
          exact s'.trans he h0
      · push_neg at h
        rw [← hs]
        constructor
        · intro ha'; exact absurd ha' (h ⟨a, ha⟩)
        · intro he; exact absurd he (ne_of_lt (cf_idx_lt s _))
    rcases cf_fin_cases i with hi | rfl <;> rcases cf_fin_cases j with hj | rfl
    · rw [cf_extd_rel_lt s c i j hi hj, hres i j hi hj]
    · rw [cf_extd_rel_last s c i hi, hlast i hi]
    · rw [Setoid.comm' (cfExtd s c), Setoid.comm' s', cf_extd_rel_last s c j hj, hlast j hj]
    · exact ⟨fun _ => s'.refl _, fun _ => (cfExtd s c).refl _⟩



lemma cf_bs_lab {m : ℕ} (s : Setoid (Fin m)) (g : Fin m → ℕ) (K : ℕ) (hker : ∀ i j, s i j ↔ g i = g j)
    (himg : Finset.univ.image g = Finset.range K) :
    blockSizes s = (Finset.range K).val.map (fun d => (Finset.univ.filter (fun i => g i = d)).card) := by
  have hb : blocks s = (Finset.range K).image (fun d => Finset.univ.filter (fun i => g i = d)) := by
    rw [← himg, Finset.image_image, cf_blocks_eq]
    apply Finset.image_congr
    intro i _
    ext j; simp only [cls, Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply, hker]
    exact eq_comm
  have hinj : Set.InjOn (fun d => Finset.univ.filter (fun i => g i = d)) (Finset.range K : Set ℕ) := by
    intro d hd d' _ hdd
    simp only [Finset.coe_range, Set.mem_Iio] at hd
    have : d ∈ Finset.univ.image g := by rw [himg]; exact Finset.mem_range.2 hd
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 this
    have hi : i ∈ Finset.univ.filter (fun j => g j = g i) := by simp
    simp only at hdd
    rw [hdd] at hi; simpa using hi
  rw [blockSizes, hb, Finset.image_val_of_injOn hinj, Multiset.map_map]
  rfl

lemma cf_pdEPF_range (α θ : ℝ) (K : ℕ) (f : ℕ → ℕ) :
    pdEPF α θ ((Finset.range K).val.map f) =
      (∏ i ∈ Finset.Ico 1 K, (θ + (i : ℝ) * α)) / (ascPochhammer ℝ ((∑ d ∈ Finset.range K, f d) - 1)).eval (θ + 1) *
        ∏ d ∈ Finset.range K, (ascPochhammer ℝ (f d - 1)).eval (1 - α) := by
  unfold pdEPF
  simp [Multiset.map_map, Finset.sum_map_val, Finset.prod_map_val]
  rfl

lemma cf_rec_old (α θ : ℝ) (n k c : ℕ) (f f' : ℕ → ℕ) (hn : 1 ≤ n) (hθn : (n : ℝ) + θ ≠ 0)
    (hsum : ∑ d ∈ Finset.range k, f d = n) (hc : c < k) (hpos : 1 ≤ f c)
    (hf' : ∀ d, d ≠ c → f' d = f d) (hfc : f' c = f c + 1) :
    pdEPF α θ ((Finset.range k).val.map f') =
      pdEPF α θ ((Finset.range k).val.map f) * (((f c : ℝ) - α) / (n + θ)) := by
  rw [cf_pdEPF_range, cf_pdEPF_range]
  have hcm := Finset.mem_range.2 hc
  have hs' : ∑ d ∈ Finset.range k, f' d = n + 1 := by
    have h1 := Finset.add_sum_erase (Finset.range k) f' hcm
    have h2 := Finset.add_sum_erase (Finset.range k) f hcm
    have h3 : ∑ x ∈ (Finset.range k).erase c, f' x = ∑ x ∈ (Finset.range k).erase c, f x :=
      Finset.sum_congr rfl (fun d hd => hf' d (Finset.ne_of_mem_erase hd))
    omega
  have hP : ∏ d ∈ Finset.range k, (ascPochhammer ℝ (f' d - 1)).eval (1 - α) =
      (ascPochhammer ℝ (f c)).eval (1 - α) *
        ∏ d ∈ (Finset.range k).erase c, (ascPochhammer ℝ (f d - 1)).eval (1 - α) := by
    rw [← Finset.mul_prod_erase _ _ hcm, hfc, Nat.add_sub_cancel]
    congr 1
    apply Finset.prod_congr rfl
    intro d hd; rw [hf' d (Finset.ne_of_mem_erase hd)]
  have hQ : ∏ d ∈ Finset.range k, (ascPochhammer ℝ (f d - 1)).eval (1 - α) =
      (ascPochhammer ℝ (f c - 1)).eval (1 - α) *
        ∏ d ∈ (Finset.range k).erase c, (ascPochhammer ℝ (f d - 1)).eval (1 - α) :=
    (Finset.mul_prod_erase _ _ hcm).symm
  rw [hs', hsum, hP, hQ]
  generalize ∏ d ∈ (Finset.range k).erase c, (ascPochhammer ℝ (f d - 1)).eval (1 - α) = R
  generalize ∏ i ∈ Finset.Ico 1 k, (θ + (i : ℝ) * α) = A
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨e, he⟩ : ∃ e, f c = e + 1 := ⟨f c - 1, by omega⟩
  rw [he]
  simp only [Nat.add_sub_cancel, ascPochhammer_succ_eval]
  have h2 : θ + 1 + (m : ℝ) ≠ 0 := by push_cast at hθn; intro h; apply hθn; linarith
  push_cast at hθn ⊢
  field_simp
  ring

lemma cf_rec_new (α θ : ℝ) (n k : ℕ) (f f' : ℕ → ℕ) (hn : 1 ≤ n) (hθn : (n : ℝ) + θ ≠ 0)
    (hsum : ∑ d ∈ Finset.range k, f d = n) (hk : 1 ≤ k)
    (hf' : ∀ d, d < k → f' d = f d) (hfk : f' k = 1) :
    pdEPF α θ ((Finset.range (k+1)).val.map f') =
      pdEPF α θ ((Finset.range k).val.map f) * ((θ + k * α) / (n + θ)) := by
  rw [cf_pdEPF_range, cf_pdEPF_range]
  have hs' : ∑ d ∈ Finset.range (k+1), f' d = n + 1 := by
    rw [Finset.sum_range_succ, hfk, Finset.sum_congr rfl (fun d hd => hf' d (Finset.mem_range.1 hd)), hsum]
  have hP : ∏ d ∈ Finset.range (k+1), (ascPochhammer ℝ (f' d - 1)).eval (1 - α) =
      ∏ d ∈ Finset.range k, (ascPochhammer ℝ (f d - 1)).eval (1 - α) := by
    rw [Finset.prod_range_succ, hfk]
    simp only [Nat.sub_self, ascPochhammer_zero, Polynomial.eval_one, mul_one]
    apply Finset.prod_congr rfl
    intro d hd; rw [hf' d (Finset.mem_range.1 hd)]
  rw [hs', hsum, hP, Finset.prod_Ico_succ_top hk]
  generalize ∏ d ∈ Finset.range k, (ascPochhammer ℝ (f d - 1)).eval (1 - α) = R
  generalize ∏ i ∈ Finset.Ico 1 k, (θ + (i : ℝ) * α) = A
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel, ascPochhammer_succ_eval]
  have h2 : θ + 1 + (m : ℝ) ≠ 0 := by push_cast at hθn; intro h; apply hθn; linarith
  push_cast at hθn ⊢
  field_simp
  ring



noncomputable def cfSz {n : ℕ} (s : Setoid (Fin n)) (d : ℕ) : ℕ := (Finset.univ.filter (fun i => cfIdx s i = d)).card

lemma cf_img_idx {n : ℕ} (s : Setoid (Fin n)) : Finset.univ.image (cfIdx s) = Finset.range (cfk s) := by
  ext d; simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
  constructor
  · rintro ⟨i, rfl⟩; exact cf_idx_lt s i
  · intro hd; exact cf_idx_surj s d hd

lemma cf_bs_sz {n : ℕ} (s : Setoid (Fin n)) : blockSizes s = (Finset.range (cfk s)).val.map (cfSz s) :=
  cf_bs_lab s (cfIdx s) (cfk s) (fun i j => (cf_idx_iff s i j).symm) (cf_img_idx s)

lemma cf_sum_sz {n : ℕ} (s : Setoid (Fin n)) : ∑ d ∈ Finset.range (cfk s), cfSz s d = n := by
  have := Finset.card_eq_sum_card_fiberwise (f := cfIdx s) (s := Finset.univ) (t := Finset.range (cfk s))
    (fun i _ => Finset.mem_range.2 (cf_idx_lt s i))
  simp only [Finset.card_univ, Fintype.card_fin] at this
  exact this.symm

lemma cf_sz_pos {n : ℕ} (s : Setoid (Fin n)) (d : ℕ) (hd : d < cfk s) : 1 ≤ cfSz s d := by
  obtain ⟨i, hi⟩ := cf_idx_surj s d hd
  apply Finset.card_pos.2
  exact ⟨i, by simp [hi]⟩

lemma cf_k_pos {n : ℕ} (s : Setoid (Fin n)) (hn : 1 ≤ n) : 1 ≤ cfk s := by
  have := cf_idx_lt s ⟨0, hn⟩; omega

lemma cf_k_zero (s : Setoid (Fin 0)) : cfk s = 0 := by
  rcases Nat.eq_zero_or_pos (cfk s) with h | h
  · exact h
  · obtain ⟨i, _⟩ := cf_idx_surj s 0 h; exact i.elim0

noncomputable def cfW (α θ : ℝ) {n : ℕ} (s : Setoid (Fin n)) (c : ℕ) : ℝ :=
  if n = 0 then 1 else if c < cfk s then ((cfSz s c : ℝ) - α) / (n + θ) else (θ + cfk s * α) / (n + θ)

lemma cf_pd_step (α θ : ℝ) (hα1 : α < 1) (hθ : -α < θ) {n : ℕ} (s : Setoid (Fin n)) (c : ℕ)
    (hc : c ≤ cfk s) :
    pdEPF α θ (blockSizes (cfExtd s c)) = pdEPF α θ (blockSizes s) * cfW α θ s c := by
  set k := cfk s with hk
  let g : Fin (n+1) → ℕ := fun i => if h : i.val < n then cfIdx s ⟨i, h⟩ else c
  have hg_cs : ∀ i : Fin n, g (Fin.castSucc i) = cfIdx s i := by
    intro i; simp only [g, Fin.val_castSucc, i.2, dif_pos]
  have hg_last : g (Fin.last n) = c := by simp [g]
  let K := if c < k then k else k + 1
  have himg : Finset.univ.image g = Finset.range K := by
    ext d
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range, K]
    constructor
    · rintro ⟨i, rfl⟩
      rcases cf_fin_cases i with hi | rfl
      · have : g i = cfIdx s ⟨i, hi⟩ := by simp [g, hi]
        rw [this]; have := cf_idx_lt s ⟨i, hi⟩; split_ifs <;> omega
      · rw [hg_last]; split_ifs <;> omega
    · intro hd
      by_cases hdk : d < k
      · obtain ⟨i, hi⟩ := cf_idx_surj s d hdk
        exact ⟨Fin.castSucc i, by rw [hg_cs, hi]⟩
      · refine ⟨Fin.last n, ?_⟩
        rw [hg_last]; split_ifs at hd <;> omega
  have hbs := cf_bs_lab (cfExtd s c) g K (fun i j => Iff.rfl) himg
  have hsz : ∀ d, (Finset.univ.filter (fun i => g i = d)).card = cfSz s d + if c = d then 1 else 0 := by
    intro d
    rw [Finset.card_filter, Fin.sum_univ_castSucc, cfSz, Finset.card_filter]
    simp only [hg_cs, hg_last]
  have hfun : (fun d => (Finset.univ.filter (fun i => g i = d)).card) =
      fun d => cfSz s d + if c = d then 1 else 0 := funext hsz
  rw [hbs, hfun, cf_bs_sz s, ← hk]
  unfold cfW
  rw [← hk]
  by_cases hn : n = 0
  · subst hn
    have hk0 : k = 0 := cf_k_zero s
    have hc0 : c = 0 := by omega
    simp only [K, hk0, hc0, lt_irrefl, if_false, if_true]
    rw [cf_pdEPF_range, cf_pdEPF_range]
    simp [cfSz]
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 hn
  have hθn : (n : ℝ) + θ ≠ 0 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    intro h; linarith
  rw [if_neg hn]
  by_cases hck : c < k
  · simp only [K, hck, if_true]
    apply cf_rec_old α θ n k c (cfSz s) _ hn1 hθn (cf_sum_sz s) hck (cf_sz_pos s c hck)
    · intro d hd; rw [if_neg (Ne.symm hd), add_zero]
    · rw [if_pos rfl]
  · have hck' : c = k := by omega
    simp only [K, hck, if_false]
    apply cf_rec_new α θ n k (cfSz s) _ hn1 hθn (cf_sum_sz s) (cf_k_pos s hn1)
    · intro d hd; rw [if_neg (by omega), add_zero]
    · rw [if_pos hck']
      have : cfSz s k = 0 := by
        rw [cfSz, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro i _; have := cf_idx_lt s i; omega
      rw [this]



noncomputable def cfBnd (α θ : ℝ) {n : ℕ} (s : Setoid (Fin n)) (c : ℕ) : ℝ :=
  ∑ d ∈ Finset.range c, ((cfSz s d : ℝ) - α) / (n + θ)

noncomputable def cfTop (α θ : ℝ) {n : ℕ} (s : Setoid (Fin n)) (c : ℕ) : ℝ :=
  if c < cfk s then cfBnd α θ s (c + 1) else 1

lemma cf_ch_ex (α θ : ℝ) {n : ℕ} (s : Setoid (Fin n)) (x : ℝ) :
    ∃ d, cfk s ≤ d ∨ x < cfBnd α θ s (d + 1) := ⟨cfk s, Or.inl le_rfl⟩

noncomputable def cfCh (α θ : ℝ) {n : ℕ} (s : Setoid (Fin n)) (x : ℝ) : ℕ := Nat.find (cf_ch_ex α θ s x)

lemma cf_ch_le (α θ : ℝ) {n : ℕ} (s : Setoid (Fin n)) (x : ℝ) : cfCh α θ s x ≤ cfk s :=
  Nat.find_min' _ (Or.inl le_rfl)

lemma cf_measurable_ch (α θ : ℝ) {n : ℕ} (s : Setoid (Fin n)) : Measurable (cfCh α θ s) := by
  apply measurable_find (p := fun x d => cfk s ≤ d ∨ x < cfBnd α θ s (d + 1))
  intro d
  exact (MeasurableSet.const _).union measurableSet_Iio

section params
variable (α θ : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hθ : -α < θ)
include hα0 hα1 hθ

lemma cf_w_nonneg {n : ℕ} (s : Setoid (Fin n)) (d : ℕ) (hd : d < cfk s) :
    0 ≤ ((cfSz s d : ℝ) - α) / (n + θ) := by
  obtain ⟨i, _⟩ := cf_idx_surj s d hd
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast Fin.pos i
  have h1 : (1 : ℝ) ≤ cfSz s d := by exact_mod_cast cf_sz_pos s d hd
  apply div_nonneg <;> linarith

lemma cf_bnd_mono {n : ℕ} (s : Setoid (Fin n)) (d d' : ℕ) (h : d ≤ d') (h' : d' ≤ cfk s) :
    cfBnd α θ s d ≤ cfBnd α θ s d' := by
  unfold cfBnd
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 h)
  intro e he _
  exact cf_w_nonneg α θ hα0 hα1 hθ s e (by simp at he; omega)

lemma cf_bnd_zero {n : ℕ} (s : Setoid (Fin n)) : cfBnd α θ s 0 = 0 := by simp [cfBnd]

lemma cf_bnd_k {n : ℕ} (s : Setoid (Fin n)) (hn : 1 ≤ n) :
    cfBnd α θ s (cfk s) = ((n : ℝ) - cfk s * α) / (n + θ) := by
  unfold cfBnd
  rw [← Finset.sum_div, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  congr 1
  exact_mod_cast cf_sum_sz s

lemma cf_bnd_le_one {n : ℕ} (s : Setoid (Fin n)) : cfBnd α θ s (cfk s) ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [cf_k_zero s, cf_bnd_zero α θ hα0 hα1 hθ]; norm_num
  rw [cf_bnd_k α θ hα0 hα1 hθ s hn]
  have hk : (1 : ℝ) ≤ cfk s := by exact_mod_cast cf_k_pos s hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [div_le_one (by linarith)]
  nlinarith

lemma cf_ch_set {n : ℕ} (s : Setoid (Fin n)) (c : ℕ) (hc : c ≤ cfk s) :
    {x | cfCh α θ s x = c} ∩ Set.Ico 0 1 = Set.Ico (cfBnd α θ s c) (cfTop α θ s c) := by
  have hbk := cf_bnd_le_one α θ hα0 hα1 hθ s
  ext x
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Ico, cfCh, Nat.find_eq_iff, cfTop]
  constructor
  · rintro ⟨⟨hP, hlt⟩, hx0, hx1⟩
    refine ⟨?_, ?_⟩
    · rcases Nat.eq_zero_or_pos c with rfl | hc0
      · rw [cf_bnd_zero α θ hα0 hα1 hθ]; exact hx0
      · have := hlt (c - 1) (by omega)
        push_neg at this
        have e : c - 1 + 1 = c := by omega
        rw [e] at this; exact this.2
    · split_ifs with hck
      · rcases hP with h | h
        · omega
        · exact h
      · exact hx1
  · rintro ⟨h1, h2⟩
    have hb0 : 0 ≤ cfBnd α θ s c := by
      rw [← cf_bnd_zero α θ hα0 hα1 hθ s]; exact cf_bnd_mono α θ hα0 hα1 hθ s 0 c (Nat.zero_le _) hc
    refine ⟨⟨?_, ?_⟩, by linarith, ?_⟩
    · split_ifs at h2 with hck
      · exact Or.inr h2
      · exact Or.inl (by omega)
    · intro d hd
      push_neg
      refine ⟨by omega, ?_⟩
      exact le_trans (cf_bnd_mono α θ hα0 hα1 hθ s (d + 1) c (by omega) hc) h1
    · split_ifs at h2 with hck
      · exact lt_of_lt_of_le h2 (le_trans (cf_bnd_mono α θ hα0 hα1 hθ s (c + 1) (cfk s) (by omega) le_rfl) hbk)
      · exact h2

lemma cf_top_sub {n : ℕ} (s : Setoid (Fin n)) (c : ℕ) (hc : c ≤ cfk s) :
    cfTop α θ s c - cfBnd α θ s c = cfW α θ s c := by
  unfold cfTop cfW
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hk := cf_k_zero s
    have : c = 0 := by omega
    subst this
    simp [hk, cf_bnd_zero α θ hα0 hα1 hθ]
  simp only [show n ≠ 0 by omega, if_false]
  by_cases hck : c < cfk s
  · simp only [hck, if_true]
    unfold cfBnd; rw [Finset.sum_range_succ]; ring
  · simp only [hck, if_false]
    have : c = cfk s := by omega
    subst this
    rw [cf_bnd_k α θ hα0 hα1 hθ s hn]
    have hθn : (n : ℝ) + θ ≠ 0 := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      intro h; linarith
    field_simp
    ring

lemma cf_top_ge {n : ℕ} (s : Setoid (Fin n)) (c : ℕ) (hc : c ≤ cfk s) :
    cfBnd α θ s c ≤ cfTop α θ s c := by
  unfold cfTop
  split_ifs with hck
  · exact cf_bnd_mono α θ hα0 hα1 hθ s c (c+1) (by omega) (by omega)
  · exact le_trans (cf_bnd_mono α θ hα0 hα1 hθ s c (cfk s) hc le_rfl) (cf_bnd_le_one α θ hα0 hα1 hθ s)

noncomputable def cfU : Measure ℝ := volume.restrict (Set.Ico (0:ℝ) 1)

omit hα0 hα1 hθ in
instance cf_U_prob : IsProbabilityMeasure cfU := ⟨by simp [cfU]⟩

lemma cf_U_ch {n : ℕ} (s : Setoid (Fin n)) (c : ℕ) (hc : c ≤ cfk s) :
    cfU.real {x | cfCh α θ s x = c} = cfW α θ s c := by
  have hm : MeasurableSet {x | cfCh α θ s x = c} := (cf_measurable_ch α θ s) (measurableSet_singleton c)
  rw [measureReal_def, cfU, Measure.restrict_apply hm,
    cf_ch_set α θ hα0 hα1 hθ s c hc, Real.volume_Ico, cf_top_sub α θ hα0 hα1 hθ s c hc,
    ENNReal.toReal_ofReal]
  rw [← cf_top_sub α θ hα0 hα1 hθ s c hc]; linarith [cf_top_ge α θ hα0 hα1 hθ s c hc]

end params



noncomputable def cfSt (α θ : ℝ) (u : ℕ → ℝ) : (n : ℕ) → Setoid (Fin n)
  | 0 => ⊥
  | n+1 => cfExtd (cfSt α θ u n) (cfCh α θ (cfSt α θ u n) (u n))

lemma cf_fin0_eq (s t : Setoid (Fin 0)) : s = t := Setoid.ext (fun i => i.elim0)

lemma cf_st_set (α θ : ℝ) (n : ℕ) (s' : Setoid (Fin (n+1))) :
    {u : ℕ → ℝ | cfSt α θ u (n+1) = s'} =
      {u | cfSt α θ u n = cfRes s'} ∩ (fun u : ℕ → ℝ => u n) ⁻¹' {x | cfCh α θ (cfRes s') x = cfCstar s'} := by
  ext u
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
  show cfExtd (cfSt α θ u n) (cfCh α θ (cfSt α θ u n) (u n)) = s' ↔ _
  constructor
  · intro h
    have h1 : cfSt α θ u n = cfRes s' := by rw [← h, cf_res_extd]
    refine ⟨h1, ?_⟩
    rw [h1] at h
    exact (cf_extd_iff s' _ (cf_ch_le α θ _ _)).1 h
  · rintro ⟨h1, h2⟩
    rw [h1, h2]
    exact (cf_extd_iff s' _ (cf_cstar_le s')).2 rfl

def cfFil (n : ℕ) : MeasurableSpace (ℕ → ℝ) :=
  ⨆ i ∈ Set.Iio n, MeasurableSpace.comap (fun u : ℕ → ℝ => u i) inferInstance

lemma cf_F_le (n : ℕ) : cfFil n ≤ MeasurableSpace.pi :=
  iSup₂_le fun i _ => (measurable_pi_apply i).comap_le

lemma cf_F_mono (n : ℕ) : cfFil n ≤ cfFil (n+1) :=
  biSup_mono fun i hi => by simp only [Set.mem_Iio] at hi ⊢; omega

lemma cf_eval_meas (n : ℕ) (B : Set ℝ) (hB : MeasurableSet B) (S : Set ℕ) (hn : n ∈ S) :
    MeasurableSet[⨆ i ∈ S, MeasurableSpace.comap (fun u : ℕ → ℝ => u i) inferInstance]
      ((fun u : ℕ → ℝ => u n) ⁻¹' B) := by
  have : MeasurableSet[MeasurableSpace.comap (fun u : ℕ → ℝ => u n) inferInstance]
      ((fun u : ℕ → ℝ => u n) ⁻¹' B) := ⟨B, hB, rfl⟩
  exact (le_iSup₂ (f := fun i (_ : i ∈ S) => MeasurableSpace.comap (fun u : ℕ → ℝ => u i) inferInstance) n hn) _ this

lemma cf_st_measF (α θ : ℝ) : ∀ (n : ℕ) (s : Setoid (Fin n)),
    MeasurableSet[cfFil n] {u : ℕ → ℝ | cfSt α θ u n = s} := by
  intro n
  induction n with
  | zero =>
    intro s
    have : {u : ℕ → ℝ | cfSt α θ u 0 = s} = Set.univ := by
      ext u; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]; exact cf_fin0_eq _ _
    rw [this]; exact MeasurableSet.univ
  | succ n ih =>
    intro s'
    rw [cf_st_set]
    apply MeasurableSet.inter
    · exact cf_F_mono n _ (ih _)
    · exact cf_eval_meas n _ ((cf_measurable_ch α θ _) (measurableSet_singleton _)) _ (by simp)

lemma cf_st_meas (α θ : ℝ) (n : ℕ) (s : Setoid (Fin n)) :
    MeasurableSet {u : ℕ → ℝ | cfSt α θ u n = s} := cf_F_le n _ (cf_st_measF α θ n s)

lemma cf_st_prob (α θ : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hθ : -α < θ) :
    ∀ (n : ℕ) (s : Setoid (Fin n)),
      (Measure.infinitePi (fun _ : ℕ => cfU)).real {u : ℕ → ℝ | cfSt α θ u n = s} = pdEPF α θ (blockSizes s) := by
  have hind : ProbabilityTheory.iIndep (fun i : ℕ => MeasurableSpace.comap (fun u : ℕ → ℝ => u i) inferInstance)
      (Measure.infinitePi (fun _ : ℕ => cfU)) :=
    (ProbabilityTheory.iIndepFun_infinitePi (P := fun _ : ℕ => cfU) (X := fun _ (x : ℝ) => x)
      (fun _ => measurable_id)).iIndep
  intro n
  induction n with
  | zero =>
    intro s
    have : {u : ℕ → ℝ | cfSt α θ u 0 = s} = Set.univ := by
      ext u; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]; exact cf_fin0_eq _ _
    rw [this, measureReal_def, measure_univ, ENNReal.toReal_one]
    have hb : blockSizes s = 0 := by
      simp [blockSizes, blocks]
    rw [hb]; simp [pdEPF]
  | succ n ih =>
    intro s'
    rw [cf_st_set]
    have hI := (ProbabilityTheory.Indep_iff _ _ _).1
      (ProbabilityTheory.indep_iSup_of_disjoint (fun i => (measurable_pi_apply i).comap_le) hind
        (S := Set.Iio n) (T := {n}) (by simp))
    have hB : MeasurableSet {x | cfCh α θ (cfRes s') x = cfCstar s'} :=
      (cf_measurable_ch α θ _) (measurableSet_singleton _)
    rw [measureReal_def, hI _ _ (cf_st_measF α θ n _) (cf_eval_meas n _ hB _ (by simp)),
      ENNReal.toReal_mul, ← measureReal_def, ih]
    rw [← Measure.map_apply (measurable_pi_apply n) hB, Measure.infinitePi_map_eval, ← measureReal_def,
      cf_U_ch α θ hα0 hα1 hθ _ _ (cf_cstar_le s'), ← cf_pd_step α θ hα1 hθ _ _ (cf_cstar_le s'),
      (cf_extd_iff s' _ (cf_cstar_le s')).2 rfl]

/-- consistency of the process -/
lemma cf_st_cons (α θ : ℝ) (u : ℕ → ℝ) : ∀ (m n : ℕ) (h : n ≤ m) (i j : Fin n),
    cfSt α θ u m (Fin.castLE h i) (Fin.castLE h j) ↔ cfSt α θ u n i j := by
  intro m
  induction m with
  | zero => intro n h i; have : n = 0 := by omega
            subst this; exact i.elim0
  | succ m ih =>
    intro n h i j
    rcases Nat.lt_or_ge n (m+1) with hn | hn
    · have hle : n ≤ m := by omega
      show cfExtd (cfSt α θ u m) _ (Fin.castLE h i) (Fin.castLE h j) ↔ _
      rw [cf_extd_rel_lt _ _ _ _ (by simp; omega) (by simp; omega)]
      exact ih n hle i j
    · have : n = m + 1 := by omega
      subst this
      rfl

lemma cf_idx_local {m n : ℕ} (h : n ≤ m) (s : Setoid (Fin m)) (t : Setoid (Fin n))
    (hst : ∀ i j : Fin n, s (Fin.castLE h i) (Fin.castLE h j) ↔ t i j) (i : Fin n) :
    cfIdx s (Fin.castLE h i) = cfIdx t i := by
  unfold cfIdx
  apply cf_bi_local (cfExt s) (cfExt t) n _ i i.2
  intro a b ha hb
  have h1 := cf_ext_rel s ⟨a, by omega⟩ ⟨b, by omega⟩
  have h2 := cf_ext_rel t ⟨a, ha⟩ ⟨b, hb⟩
  simp only at h1 h2
  rw [h1, h2]
  exact hst ⟨a, ha⟩ ⟨b, hb⟩

noncomputable def cfLab (α θ : ℝ) (u : ℕ → ℝ) (i : ℕ) : ℕ := cfIdx (cfSt α θ u (i+1)) (Fin.last i)

noncomputable def cfPi (α θ : ℝ) (u : ℕ → ℝ) : PI := Setoid.ker (cfLab α θ u)

lemma cf_lab_eq (α θ : ℝ) (u : ℕ → ℝ) (n : ℕ) (i : Fin n) : cfLab α θ u i = cfIdx (cfSt α θ u n) i := by
  have h : (i : ℕ) + 1 ≤ n := i.2
  have := cf_idx_local h (cfSt α θ u n) (cfSt α θ u (i+1)) (cf_st_cons α θ u n (i+1) h) (Fin.last i)
  rw [cfLab, ← this]
  congr 1

lemma cf_restrict_pi (α θ : ℝ) (u : ℕ → ℝ) (n : ℕ) : restrict n (cfPi α θ u) = cfSt α θ u n := by
  apply Setoid.ext
  intro i j
  show cfLab α θ u i = cfLab α θ u j ↔ _
  rw [cf_lab_eq α θ u n i, cf_lab_eq α θ u n j, cf_idx_iff]

lemma cf_measurable_lab (α θ : ℝ) (i : ℕ) : Measurable (fun u : ℕ → ℝ => cfLab α θ u i) := by
  have hst : Measurable (fun u : ℕ → ℝ => cfSt α θ u (i+1)) :=
    measurable_to_countable' (fun s => cf_st_meas α θ (i+1) s)
  exact (Measurable.of_discrete (f := fun s : Setoid (Fin (i+1)) => cfIdx s (Fin.last i))).comp hst

lemma cf_measurable_pi (α θ : ℝ) : Measurable (cfPi α θ) := by
  apply cf_measurable_of
  intro i j
  exact measurableSet_eq_fun (cf_measurable_lab α θ i) (cf_measurable_lab α θ j)

theorem lemma_9_exists_core (α θ : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hθ : -α < θ) :
    ∃ μ : Measure LambdaCoalescent.Rates.PInf, IsProbabilityMeasure μ ∧ IsEPFLaw (pdEPF α θ) μ := by
  refine ⟨(Measure.infinitePi (fun _ : ℕ => cfU)).map (cfPi α θ),
    Measure.isProbabilityMeasure_map (cf_measurable_pi α θ).aemeasurable, ?_⟩
  intro n s
  rw [measureReal_def, Measure.map_apply (cf_measurable_pi α θ) (cf_meas_restrict_set n s), ← measureReal_def]
  have : cfPi α θ ⁻¹' {π : LambdaCoalescent.Rates.PInf | restrict n π = s} = {u | cfSt α θ u n = s} := by
    ext u; simp only [Set.mem_preimage, Set.mem_setOf_eq, cf_restrict_pi]
  rw [this, cf_st_prob α θ hα0 hα1 hθ n s]


end LambdaCoalescent.CoagFrag

open LambdaCoalescent.CoagFrag
open MeasureTheory

theorem solution (α θ : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hθ : -α < θ) :
    ∃ μ : Measure LambdaCoalescent.Rates.PInf, IsProbabilityMeasure μ ∧ IsEPFLaw (pdEPF α θ) μ := by
  exact lemma_9_exists_core α θ hα0 hα1 hθ
