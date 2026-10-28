-- Prove2me | solution 1 for MatroidProphetKW.Inter.eq_14
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T20:01:38.796483+00:00
-- url     : https://prove2.me/submissions/a95da668-ac90-47f1-9743-af1866c451f9

import Mathlib
import Definitions.Def_MatroidProphetKW_Inter_Setting
import Definitions.Def_MatroidProphetKW_Inter_Online

set_option autoImplicit false

open MeasureTheory

/-! ## Discrete measurability toolkit -/

theorem pvf1_ms_of_disc {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] (f : Ω → ι)
    (hf : ∀ i, MeasurableSet {w | f w = i}) (t : Set ι) : MeasurableSet {w | f w ∈ t} := by
  have : {w | f w ∈ t} = ⋃ i ∈ t, {w | f w = i} := by ext w; simp
  rw [this]
  exact MeasurableSet.biUnion t.to_countable (fun i _ => hf i)

theorem pvf1_ms_comp {Ω ι β : Type*} [MeasurableSpace Ω] [Countable ι] (f : Ω → ι)
    (hf : ∀ i, MeasurableSet {w | f w = i}) (g : ι → Ω → β) (s : Set β)
    (hg : ∀ i, MeasurableSet {w | g i w ∈ s}) : MeasurableSet {w | g (f w) w ∈ s} := by
  have : {w | g (f w) w ∈ s} = ⋃ i, ({w | f w = i} ∩ {w | g i w ∈ s}) := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h; exact ⟨f w, rfl, h⟩
    · rintro ⟨i, hi, h⟩; subst hi; exact h
  rw [this]
  exact MeasurableSet.iUnion fun i => (hf i).inter (hg i)

theorem pvf1_meas_comp {Ω ι β : Type*} [MeasurableSpace Ω] [MeasurableSpace β] [Countable ι]
    (f : Ω → ι) (hf : ∀ i, MeasurableSet {w | f w = i}) (g : ι → Ω → β)
    (hg : ∀ i, Measurable (g i)) : Measurable (fun w => g (f w) w) :=
  fun _ hs => pvf1_ms_comp f hf g _ (fun i => hg i hs)

/-- discrete measurability of a composite `g (f w) w` with discrete values -/
theorem pvf1_dm_comp {Ω ι κ : Type*} [MeasurableSpace Ω] [Countable ι]
    (f : Ω → ι) (hf : ∀ i, MeasurableSet {w | f w = i}) (g : ι → Ω → κ)
    (hg : ∀ i k, MeasurableSet {w | g i w = k}) (k : κ) :
    MeasurableSet {w | g (f w) w = k} :=
  pvf1_ms_comp f hf g {k} (fun i => hg i k)

theorem pvf1_ms_ite {Ω β : Type*} [MeasurableSpace Ω] (c : Ω → Prop) [∀ w, Decidable (c w)]
    (hc : MeasurableSet {w | c w}) (a b : β) (s : Set β) :
    MeasurableSet {w | (if c w then a else b) ∈ s} := by
  have : {w | (if c w then a else b) ∈ s} =
      ({w | c w} ∩ {_w | a ∈ s}) ∪ ({w | c w}ᶜ ∩ {_w | b ∈ s}) := by
    ext w; by_cases h : c w <;> simp [h]
  rw [this]
  exact (hc.inter (MeasurableSet.const _)).union (hc.compl.inter (MeasurableSet.const _))

theorem pvf1_dm_fst {Ω Ω' ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] (f : Ω → ι)
    (hf : ∀ i, MeasurableSet {w | f w = i}) (i : ι) :
    MeasurableSet {ω : Ω × Ω' | f ω.1 = i} := measurable_fst (hf i)

theorem pvf1_dm_snd {Ω Ω' ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] (f : Ω' → ι)
    (hf : ∀ i, MeasurableSet {w | f w = i}) (i : ι) :
    MeasurableSet {ω : Ω × Ω' | f ω.2 = i} := measurable_snd (hf i)

section Infra

open MatroidProphetKW.Inter

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem pvf1_wt_meas (S : Finset α) :
    Measurable (fun w : α → ℝ => MatroidProphetKW.Single.wt w S) := by
  unfold MatroidProphetKW.Single.wt
  exact Finset.measurable_sum _ (fun x _ => measurable_pi_apply x)

theorem pvf1_argmax_ms (P : (α → ℝ) → Finset α → Prop) (f : (α → ℝ) → Finset α → ℝ)
    (hP : ∀ S, MeasurableSet {w | P w S}) (hf : ∀ S, Measurable (fun w => f w S))
    (S0 : Finset α) : MeasurableSet {w | argmaxOn (P w) (f w) = S0} := by
  classical
  let cond : (α → ℝ) → Finset α → Prop := fun w S => P w S ∧ ∀ T, P w T → f w T ≤ f w S
  have hcond : ∀ S, MeasurableSet {w | cond w S} := by
    intro S
    have : {w | cond w S} = {w | P w S} ∩ ⋂ T, ({w | P w T}ᶜ ∪ {w | f w T ≤ f w S}) := by
      ext w
      simp only [cond, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_union,
        Set.mem_compl_iff]
      exact and_congr_right' (forall_congr' fun T => imp_iff_not_or)
    rw [this]
    exact (hP S).inter
      (MeasurableSet.iInter fun T => (hP T).compl.union (measurableSet_le (hf T) (hf S)))
  let Φ : (α → ℝ) → Finset (Finset α) := fun w => Finset.univ.filter (fun S => cond w S)
  have hΦ : ∀ 𝒮, MeasurableSet {w | Φ w = 𝒮} := by
    intro 𝒮
    have : {w | Φ w = 𝒮} = ⋂ S, {w | cond w S ↔ S ∈ 𝒮} := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Φ, Finset.ext_iff, Finset.mem_filter,
        Finset.mem_univ, true_and]
    rw [this]
    refine MeasurableSet.iInter fun S => ?_
    by_cases hS : S ∈ 𝒮
    · simp only [hS, iff_true]; exact hcond S
    · simp only [hS, iff_false]; exact (hcond S).compl
  have key : ∀ w, argmaxOn (P w) (f w) = firstOf (Φ w) := by
    intro w
    unfold argmaxOn
    congr 1
  simp only [key]
  exact pvf1_dm_comp Φ hΦ (fun 𝒮 _ => firstOf 𝒮) (fun _ _ => MeasurableSet.const _) S0

theorem pvf1_B_ms {p : ℕ} (M : Fin p → Matroid α) (S0 : Finset α) :
    MeasurableSet {w : α → ℝ | B M w = S0} :=
  pvf1_argmax_ms (fun _ S => IsIndep M S) (fun w S => MatroidProphetKW.Single.wt w S)
    (fun _ => MeasurableSet.const _) pvf1_wt_meas S0

theorem pvf1_Rj_ms {p : ℕ} (M : Fin p → Matroid α) (j : Fin p) (A S0 : Finset α) :
    MeasurableSet {w : α → ℝ | Rj M j A w = S0} := by
  unfold Rj
  refine pvf1_argmax_ms _ (fun w S => MatroidProphetKW.Single.wt w S) (fun R => ?_)
    pvf1_wt_meas S0
  exact pvf1_ms_of_disc (B M) (pvf1_B_ms M) {Bv | R ⊆ Bv \ A ∧ (M j).Indep (↑(A ∪ R) : Set α) ∧
      (↑Bv : Set α) ⊆ (M j).closure (↑(A ∪ R) : Set α)}

theorem pvf1_Cj_ms {p : ℕ} (M : Fin p → Matroid α) (j : Fin p) (A S0 : Finset α) :
    MeasurableSet {w : α → ℝ | Cj M j A w = S0} := by
  have : {w : α → ℝ | Cj M j A w = S0} = {w | (B M w, Rj M j A w) ∈ {q | q.1 \ q.2 = S0}} := rfl
  rw [this]
  refine pvf1_ms_of_disc (fun w => (B M w, Rj M j A w)) (fun q => ?_) _
  have : {w : α → ℝ | (B M w, Rj M j A w) = q} = {w | B M w = q.1} ∩ {w | Rj M j A w = q.2} := by
    ext w; simp [Prod.ext_iff]
  rw [this]
  exact (pvf1_B_ms M q.1).inter (pvf1_Rj_ms M j A q.2)


theorem pvf1_firstOf_mem {S : Finset (Finset α)} (h : S.Nonempty) : firstOf S ∈ S := by
  unfold firstOf
  rw [dif_pos h]
  obtain ⟨s, hs, hse⟩ :=
    Finset.mem_image.1 (Finset.min'_mem _ (h.image (Fintype.equivFin (Finset α))))
  rw [← hse, Equiv.symm_apply_apply]
  exact hs

theorem pvf1_firstOf_filter (Q : Finset α → Prop) {inst : DecidablePred Q} (h : ∃ S, Q S) :
    Q (firstOf (@Finset.filter _ Q inst Finset.univ)) := by
  obtain ⟨S, hS⟩ := h
  have hne : (@Finset.filter _ Q inst Finset.univ).Nonempty :=
    ⟨S, Finset.mem_filter.2 ⟨Finset.mem_univ _, hS⟩⟩
  exact (Finset.mem_filter.1 (pvf1_firstOf_mem hne)).2

theorem pvf1_firstOf_filter_empty (Q : Finset α → Prop) {inst : DecidablePred Q}
    (h : ¬ ∃ S, Q S) : firstOf (@Finset.filter _ Q inst Finset.univ) = ∅ := by
  unfold firstOf
  rw [dif_neg]
  rintro ⟨S, hS⟩
  exact h ⟨S, (Finset.mem_filter.1 hS).2⟩

theorem pvf1_argmaxOn_spec (P : Finset α → Prop) (f : Finset α → ℝ) (h : ∃ S, P S) :
    P (argmaxOn P f) ∧ ∀ T, P T → f T ≤ f (argmaxOn P f) := by
  classical
  obtain ⟨S0, hS0⟩ := h
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image (Finset.univ.filter P) f
    ⟨S0, Finset.mem_filter.2 ⟨Finset.mem_univ _, hS0⟩⟩
  unfold argmaxOn
  apply pvf1_firstOf_filter (fun S => P S ∧ ∀ T, P T → f T ≤ f S)
  exact ⟨S, (Finset.mem_filter.1 hS).2,
    fun T hT => hmax T (Finset.mem_filter.2 ⟨Finset.mem_univ _, hT⟩)⟩

theorem pvf1_argmaxOn_empty (P : Finset α → Prop) (f : Finset α → ℝ) (h : ¬ ∃ S, P S) :
    argmaxOn P f = ∅ := by
  classical
  unfold argmaxOn
  apply pvf1_firstOf_filter_empty
  rintro ⟨S, hS, -⟩
  exact h ⟨S, hS⟩

theorem pvf1_B_spec {p : ℕ} (M : Fin p → Matroid α) (w' : α → ℝ) :
    IsIndep M (B M w') ∧ ∀ T, IsIndep M T →
      MatroidProphetKW.Single.wt w' T ≤ MatroidProphetKW.Single.wt w' (B M w') :=
  pvf1_argmaxOn_spec _ _ ⟨∅, fun j => by simp⟩

theorem pvf1_OPT_eq {p : ℕ} (M : Fin p → Matroid α) (w' : α → ℝ) :
    OPT M w' = MatroidProphetKW.Single.wt w' (B M w') := by
  classical
  unfold OPT
  apply le_antisymm
  · apply Finset.sup'_le
    intro S hS
    exact (pvf1_B_spec M w').2 S (Finset.mem_filter.1 hS).2
  · exact Finset.le_sup' (MatroidProphetKW.Single.wt w')
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, (pvf1_B_spec M w').1⟩)

theorem pvf1_Rj_sub_B {p : ℕ} (M : Fin p → Matroid α) (j : Fin p) (A : Finset α)
    (w' : α → ℝ) : Rj M j A w' ⊆ B M w' := by
  unfold Rj
  by_cases h : ∃ R, R ⊆ B M w' \ A ∧ (M j).Indep (↑(A ∪ R) : Set α) ∧
      (↑(B M w') : Set α) ⊆ (M j).closure (↑(A ∪ R) : Set α)
  · exact ((pvf1_argmaxOn_spec _ (MatroidProphetKW.Single.wt w') h).1.1).trans
      Finset.sdiff_subset
  · rw [pvf1_argmaxOn_empty _ _ h]; exact Finset.empty_subset _


theorem pvf1_int_coord (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)]
    (hF_int : ∀ x, Integrable id (F x)) (x : α) : Integrable (fun w : α → ℝ => w x) (law F) :=
  ((measurePreserving_eval F x).integrable_comp (hF_int x).aestronglyMeasurable).2 (hF_int x)

theorem pvf1_int_absSum (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)]
    (hF_int : ∀ x, Integrable id (F x)) :
    Integrable (fun w : α → ℝ => ∑ x, |w x|) (law F) :=
  integrable_finsetSum _ (fun x _ => (pvf1_int_coord F hF_int x).abs)

theorem pvf1_abs_wt_le (w : α → ℝ) (S : Finset α) :
    |MatroidProphetKW.Single.wt w S| ≤ ∑ x, |w x| := by
  unfold MatroidProphetKW.Single.wt
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_univ_sum_of_nonneg (fun x => abs_nonneg _))

/-- `w ↦ w(D w)` is integrable for a discretely measurable set-valued `D`. -/
theorem pvf1_int_wtD (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)]
    (hF_int : ∀ x, Integrable id (F x)) (D : (α → ℝ) → Finset α)
    (hD : ∀ S, MeasurableSet {w | D w = S}) :
    Integrable (fun w => MatroidProphetKW.Single.wt w (D w)) (law F) := by
  have hm : Measurable (fun w => MatroidProphetKW.Single.wt w (D w)) :=
    pvf1_meas_comp D hD (fun S w => MatroidProphetKW.Single.wt w S) pvf1_wt_meas
  refine (pvf1_int_absSum F hF_int).mono' hm.aestronglyMeasurable (ae_of_all _ fun w => ?_)
  rw [Real.norm_eq_abs]
  exact pvf1_abs_wt_le w (D w)

theorem pvf1_mem_sel {p : ℕ} (rule : ThresholdRule α) (M : Fin p → Matroid α)
    (xs : List α) (w : α → ℝ) (k : ℕ) (x : α) (hx : x ∈ sel rule M xs w k) :
    ∃ i, ∃ h : i < xs.length, i < k ∧ xs[i] = x ∧
      IsIndep M (insert xs[i] (sel rule M xs w i)) ∧
      rule.thr (sel rule M xs w i) (xs.take i) w xs[i] ≤ w xs[i] := by
  induction k with
  | zero => simp [sel] at hx
  | succ k ih =>
    simp only [sel] at hx
    split_ifs at hx with h1 h2
    · rcases Finset.mem_insert.1 hx with hx | hx
      · exact ⟨k, h1, Nat.lt_succ_self k, hx.symm, h2⟩
      · obtain ⟨i, h, hik, h3⟩ := ih hx
        exact ⟨i, h, Nat.lt_succ_of_lt hik, h3⟩
    · obtain ⟨i, h, hik, h3⟩ := ih hx
      exact ⟨i, h, Nat.lt_succ_of_lt hik, h3⟩
    · obtain ⟨i, h, hik, h3⟩ := ih hx
      exact ⟨i, h, Nat.lt_succ_of_lt hik, h3⟩
theorem pvf1_sel_succ_sub {p : ℕ} (rule : ThresholdRule α) (M : Fin p → Matroid α)
    (xs : List α) (w : α → ℝ) (k : ℕ) : sel rule M xs w k ⊆ sel rule M xs w (k + 1) := by
  conv_rhs => simp only [sel]
  split_ifs
  · exact Finset.subset_insert _ _
  · exact subset_refl _
  · exact subset_refl _

theorem pvf1_sel_mono {p : ℕ} (rule : ThresholdRule α) (M : Fin p → Matroid α)
    (xs : List α) (w : α → ℝ) {i k : ℕ} (hik : i ≤ k) :
    sel rule M xs w i ⊆ sel rule M xs w k := by
  induction k, hik using Nat.le_induction with
  | base => exact subset_refl _
  | succ k _ ih => exact ih.trans (pvf1_sel_succ_sub rule M xs w k)

theorem pvf1_ae_nonneg (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)]
    (hF_nonneg : ∀ x, F x (Set.Iio 0) = 0) : ∀ᵐ w' ∂(law F), ∀ y, 0 ≤ w' y := by
  rw [ae_all_iff]
  intro y
  rw [ae_iff]
  have hset : {a : α → ℝ | ¬ 0 ≤ a y} = Function.eval y ⁻¹' Set.Iio 0 := by
    ext a; simp
  rw [hset]
  exact Measure.pi_eval_preimage_null F (hF_nonneg y)


/-! ## Proposition 2 (Kleinberg-Weinberg Lemma 3 + telescoping) -/

/-- Extend `R0` (with `S ∪ R0` independent) inside `D \ S` until `S ∪ R` spans `D`. -/
theorem pv34_ext (N : Matroid α) (hE : N.E = Set.univ) (D S R0 : Finset α)
    (h0 : R0 ⊆ D \ S) (hi : N.Indep (↑(S ∪ R0) : Set α)) :
    ∃ R, R0 ⊆ R ∧ R ⊆ D \ S ∧ N.Indep (↑(S ∪ R) : Set α) ∧
      (↑D : Set α) ⊆ N.closure (↑(S ∪ R) : Set α) := by
  classical
  obtain ⟨R, hR, hmax⟩ := Finset.exists_max_image
    (Finset.univ.filter (fun R => R0 ⊆ R ∧ R ⊆ D \ S ∧ N.Indep (↑(S ∪ R) : Set α)))
    Finset.card ⟨R0, Finset.mem_filter.2 ⟨Finset.mem_univ _, subset_refl _, h0, hi⟩⟩
  obtain ⟨-, h1, h2, h3⟩ := Finset.mem_filter.1 hR
  refine ⟨R, h1, h2, h3, ?_⟩
  intro b hb
  by_contra hbc
  have hbSR : b ∉ (↑(S ∪ R) : Set α) := fun h =>
    hbc (N.subset_closure _ (by rw [hE]; exact Set.subset_univ _) h)
  have hins : N.Indep (insert b (↑(S ∪ R) : Set α)) :=
    (h3.insert_indep_iff_of_notMem hbSR).2 ⟨by rw [hE]; trivial, hbc⟩
  have hbS : b ∉ S := fun h => hbSR (by simp [h])
  have hbR : b ∉ R := fun h => hbSR (by simp [h])
  have hmem : insert b R ∈ Finset.univ.filter
      (fun R => R0 ⊆ R ∧ R ⊆ D \ S ∧ N.Indep (↑(S ∪ R) : Set α)) := by
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, h1.trans (Finset.subset_insert _ _), ?_, ?_⟩
    · exact Finset.insert_subset (Finset.mem_sdiff.2 ⟨Finset.mem_coe.1 hb, hbS⟩) h2
    · have e : (↑(S ∪ insert b R) : Set α) = insert b (↑(S ∪ R) : Set α) := by
        ext z; simp only [Finset.coe_union, Finset.coe_insert, Set.mem_union, Set.mem_insert_iff,
          Finset.mem_coe]; tauto
      rw [e]; exact hins
  have := hmax _ hmem
  rw [Finset.card_insert_of_notMem hbR] at this
  omega

/-- `R_j(S)` is feasible and dominates every `R0 ⊆ B \ S` with `S ∪ R0 ∈ ℐ_j` (for `w′ ≥ 0`). -/
theorem pv34_Rj_spec {p : ℕ} (M : Fin p → Matroid α) (hE : ∀ j, (M j).E = Set.univ)
    (j : Fin p) (S : Finset α) (w' : α → ℝ) (hw : ∀ x, 0 ≤ w' x) (R0 : Finset α)
    (h0 : R0 ⊆ B M w' \ S) (hi : (M j).Indep (↑(S ∪ R0) : Set α)) :
    (Rj M j S w' ⊆ B M w' \ S ∧ (M j).Indep (↑(S ∪ Rj M j S w') : Set α)) ∧
      MatroidProphetKW.Single.wt w' R0 ≤ MatroidProphetKW.Single.wt w' (Rj M j S w') := by
  obtain ⟨R, hR0, h1, h2, h3⟩ := pv34_ext (M j) (hE j) (B M w') S R0 h0 hi
  have hs := pvf1_argmaxOn_spec (fun R => R ⊆ B M w' \ S ∧ (M j).Indep (↑(S ∪ R) : Set α) ∧
      (↑(B M w') : Set α) ⊆ (M j).closure (↑(S ∪ R) : Set α))
      (MatroidProphetKW.Single.wt w') ⟨R, h1, h2, h3⟩
  unfold Rj
  refine ⟨⟨hs.1.1, hs.1.2.1⟩, ?_⟩
  calc MatroidProphetKW.Single.wt w' R0 ≤ MatroidProphetKW.Single.wt w' R :=
        Finset.sum_le_sum_of_subset_of_nonneg hR0 (fun x _ _ => hw x)
    _ ≤ _ := hs.2 R ⟨h1, h2, h3⟩

/-- The exchange step behind Lemma 3 of the paper. -/
theorem pv34_exch (N : Matroid α) (hE : N.E = Set.univ) (D S I0 Ixy : Finset α) (x y : α)
    (w' : α → ℝ) (hxy : x ≠ y) (hxS : x ∉ S) (hyS : y ∉ S)
    (h0s : I0 ⊆ D \ S) (h0i : N.Indep (↑(S ∪ I0) : Set α))
    (hxys : Ixy ⊆ D \ insert x (insert y S))
    (hxyi : N.Indep (↑(insert x (insert y S) ∪ Ixy) : Set α)) :
    ∃ Ix Iy : Finset α, Ix ⊆ D \ insert x S ∧ N.Indep (↑(insert x S ∪ Ix) : Set α) ∧
      Iy ⊆ D \ insert y S ∧ N.Indep (↑(insert y S ∪ Iy) : Set α) ∧
      MatroidProphetKW.Single.wt w' I0 + MatroidProphetKW.Single.wt w' Ixy =
        MatroidProphetKW.Single.wt w' Ix + MatroidProphetKW.Single.wt w' Iy := by
  classical
  have hyIxy : y ∉ Ixy := fun h => by
    have := hxys h; simp only [Finset.mem_sdiff, Finset.mem_insert] at this; tauto
  have hxIxy : x ∉ Ixy := fun h => by
    have := hxys h; simp only [Finset.mem_sdiff, Finset.mem_insert] at this; tauto
  have hIxyS : ∀ z ∈ Ixy, z ∉ S := fun z h => by
    have := hxys h; simp only [Finset.mem_sdiff, Finset.mem_insert] at this; tauto
  have hIxyD : Ixy ⊆ D := fun z h => (Finset.mem_sdiff.1 (hxys h)).1
  have hI0 : ∀ z ∈ I0, z ∈ D ∧ z ∉ S := fun z h => Finset.mem_sdiff.1 (h0s h)
  by_cases hy0 : y ∈ I0
  · refine ⟨insert y Ixy, I0.erase y, ?_, ?_, ?_, ?_, ?_⟩
    · intro z hz
      rw [Finset.mem_insert] at hz
      rcases hz with rfl | hz
      · rw [Finset.mem_sdiff, Finset.mem_insert]
        exact ⟨(hI0 z hy0).1, by rintro (h | h); exacts [hxy h.symm, hyS h]⟩
      · have := hxys hz; simp only [Finset.mem_sdiff, Finset.mem_insert] at this ⊢; tauto
    · have e : (↑(insert x S ∪ insert y Ixy) : Set α) = ↑(insert x (insert y S) ∪ Ixy) := by
        ext z; simp only [Finset.coe_union, Finset.coe_insert, Set.mem_union, Set.mem_insert_iff,
          Finset.mem_coe]; tauto
      rw [e]; exact hxyi
    · intro z hz
      have h1 := hI0 z (Finset.mem_of_mem_erase hz)
      have hne := Finset.ne_of_mem_erase hz
      rw [Finset.mem_sdiff, Finset.mem_insert]
      exact ⟨h1.1, by rintro (h | h); exacts [hne h, h1.2 h]⟩
    · have e : insert y S ∪ I0.erase y = S ∪ I0 := by
        ext z; by_cases hz : z = y
        · subst hz; simp [hy0]
        · simp [hz]
      rw [e]; exact h0i
    · unfold MatroidProphetKW.Single.wt
      rw [Finset.sum_insert hyIxy, Finset.sum_erase_eq_sub hy0]
      ring
  by_cases hy2 : N.Indep (insert y (↑(S ∪ I0) : Set α))
  · refine ⟨Ixy, I0, ?_, ?_, ?_, ?_, ?_⟩
    · intro z hz
      have := hxys hz; simp only [Finset.mem_sdiff, Finset.mem_insert] at this ⊢; tauto
    · refine hxyi.subset ?_
      intro z; simp only [Finset.coe_union, Finset.coe_insert, Set.mem_union, Set.mem_insert_iff,
          Finset.mem_coe]; tauto
    · intro z hz
      have h1 := hI0 z hz
      rw [Finset.mem_sdiff, Finset.mem_insert]
      exact ⟨h1.1, by rintro (h | h); exacts [hy0 (h ▸ hz), h1.2 h]⟩
    · have e : (↑(insert y S ∪ I0) : Set α) = insert y (↑(S ∪ I0) : Set α) := by
        ext z; simp only [Finset.coe_union, Finset.coe_insert, Set.mem_union, Set.mem_insert_iff,
          Finset.mem_coe]; tauto
      rw [e]; exact hy2
    · ring
  -- the fundamental-circuit exchange
  obtain ⟨Q', hQ'⟩ : ∃ Q' : Set α, Q' = ↑(insert x S ∪ Ixy) := ⟨_, rfl⟩
  have hyP : y ∉ (↑(S ∪ I0) : Set α) := by simp [hyS, hy0]
  have hycl : y ∈ N.closure (↑(S ∪ I0) : Set α) := by
    by_contra hc
    exact hy2 ((h0i.insert_indep_iff_of_notMem hyP).2 ⟨by rw [hE]; trivial, hc⟩)
  have hQi : N.Indep Q' := by
    rw [hQ']
    refine hxyi.subset ?_
    intro z; simp only [Finset.coe_union, Finset.coe_insert, Set.mem_union, Set.mem_insert_iff,
        Finset.mem_coe]; tauto
  have hyQ : y ∉ Q' := by
    rw [hQ']; simp only [Finset.coe_union, Finset.coe_insert, Set.mem_union, Set.mem_insert_iff,
      Finset.mem_coe, not_or]
    exact ⟨⟨fun h => hxy h.symm, hyS⟩, hyIxy⟩
  have hyQcl : y ∉ N.closure Q' := by
    intro hc
    have hins : N.Indep (insert y Q') := by
      rw [hQ']
      refine hxyi.subset ?_
      intro z; simp only [Finset.coe_union, Finset.coe_insert, Set.mem_union, Set.mem_insert_iff,
          Finset.mem_coe]; tauto
    exact ((hQi.insert_indep_iff_of_notMem hyQ).1 hins).2 hc
  have hC := h0i.fundCircuit_isCircuit hycl hyP
  obtain ⟨c, hcC, hcy, hcQ⟩ : ∃ c ∈ N.fundCircuit y (↑(S ∪ I0) : Set α), c ≠ y ∧
      c ∉ N.closure Q' := by
    by_contra hcon
    push Not at hcon
    apply hyQcl
    have hsub : N.fundCircuit y (↑(S ∪ I0) : Set α) \ {y} ⊆ N.closure Q' :=
      fun c hc => hcon c hc.1 hc.2
    exact N.closure_subset_closure_of_subset_closure hsub
      (hC.mem_closure_sdiff_singleton_of_mem (N.mem_fundCircuit _ _))
  have hcP : c ∈ (↑(S ∪ I0) : Set α) := by
    rcases N.fundCircuit_subset_insert y _ hcC with h | h
    · exact absurd h hcy
    · exact h
  have hcQm : c ∉ Q' := fun h =>
    hcQ (N.subset_closure Q' (by rw [hE]; exact Set.subset_univ _) h)
  have hcS : c ∉ S := fun h => hcQm (by rw [hQ']; simp [h])
  have hcx : c ≠ x := fun h => hcQm (by rw [hQ']; simp [h])
  have hcIxy : c ∉ Ixy := fun h => hcQm (by rw [hQ']; simp [h])
  have hcI0 : c ∈ I0 := by
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hcP; tauto
  have hexch : N.Indep (insert y (↑(S ∪ I0) : Set α) \ {c}) :=
    (h0i.mem_fundCircuit_iff hycl hyP).1 hcC
  refine ⟨insert c Ixy, I0.erase c, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    rw [Finset.mem_insert] at hz
    rcases hz with rfl | hz
    · rw [Finset.mem_sdiff, Finset.mem_insert]
      exact ⟨(hI0 z hcI0).1, by rintro (h | h); exacts [hcx h, hcS h]⟩
    · have := hxys hz; simp only [Finset.mem_sdiff, Finset.mem_insert] at this ⊢; tauto
  · have e : (↑(insert x S ∪ insert c Ixy) : Set α) = insert c Q' := by
      rw [hQ']; ext z; simp only [Finset.coe_union, Finset.coe_insert, Set.mem_union,
        Set.mem_insert_iff, Finset.mem_coe]; tauto
    rw [e]; exact (hQi.insert_indep_iff_of_notMem hcQm).2 ⟨by rw [hE]; trivial, hcQ⟩
  · intro z hz
    have h1 := hI0 z (Finset.mem_of_mem_erase hz)
    rw [Finset.mem_sdiff, Finset.mem_insert]
    exact ⟨h1.1, by rintro (h | h); exacts [hy0 (h ▸ Finset.mem_of_mem_erase hz), h1.2 h]⟩
  · have e : (↑(insert y S ∪ I0.erase c) : Set α) = insert y (↑(S ∪ I0) : Set α) \ {c} := by
      ext z; by_cases hz : z = c
      · subst hz; simp [hcS, hcy]
      · simp [hz]
    rw [e]; exact hexch
  · unfold MatroidProphetKW.Single.wt
    rw [Finset.sum_insert hcIxy, Finset.sum_erase_eq_sub hcI0]
    ring

/-- Lemma 3 of the paper (one step): `f(S) - f(S+x) ≤ f(S+y) - f(S+x+y)`. -/
theorem pv34_submod {p : ℕ} (M : Fin p → Matroid α) (hE : ∀ j, (M j).E = Set.univ)
    (j : Fin p) (w' : α → ℝ) (hw : ∀ x, 0 ≤ w' x) (S : Finset α) (x y : α) (hxy : x ≠ y)
    (hxS : x ∉ S) (hyS : y ∉ S) (hind : (M j).Indep (↑(insert x (insert y S)) : Set α)) :
    MatroidProphetKW.Single.wt w' (Rj M j S w') +
        MatroidProphetKW.Single.wt w' (Rj M j (insert x (insert y S)) w') ≤
      MatroidProphetKW.Single.wt w' (Rj M j (insert x S) w') +
        MatroidProphetKW.Single.wt w' (Rj M j (insert y S) w') := by
  have hS : (M j).Indep (↑(S ∪ ∅) : Set α) := hind.subset (by
    intro z; simp only [Finset.union_empty, Finset.coe_insert, Set.mem_insert_iff,
      Finset.mem_coe]; tauto)
  have hS2 : (M j).Indep (↑(insert x (insert y S) ∪ ∅) : Set α) := by
    rw [Finset.union_empty]; exact hind
  obtain ⟨⟨h0s, h0i⟩, -⟩ := pv34_Rj_spec M hE j S w' hw ∅ (Finset.empty_subset _) hS
  obtain ⟨⟨hxys, hxyi⟩, -⟩ :=
    pv34_Rj_spec M hE j (insert x (insert y S)) w' hw ∅ (Finset.empty_subset _) hS2
  obtain ⟨Ix, Iy, h1, h2, h3, h4, h5⟩ := pv34_exch (M j) (hE j) (B M w') S (Rj M j S w')
    (Rj M j (insert x (insert y S)) w') x y w' hxy hxS hyS h0s h0i hxys hxyi
  have k1 := (pv34_Rj_spec M hE j (insert x S) w' hw Ix h1 h2).2
  have k2 := (pv34_Rj_spec M hE j (insert y S) w' hw Iy h3 h4).2
  linarith

/-- Iterated: marginal losses grow along `S ⊆ T`. -/
theorem pv34_marg_union {p : ℕ} (M : Fin p → Matroid α) (hE : ∀ j, (M j).E = Set.univ)
    (j : Fin p) (w' : α → ℝ) (hw : ∀ x, 0 ≤ w' x) (S : Finset α) (x : α) (U : Finset α) :
    Disjoint S U → x ∉ S ∪ U → (M j).Indep (↑(insert x (S ∪ U)) : Set α) →
    MatroidProphetKW.Single.wt w' (Rj M j S w') -
        MatroidProphetKW.Single.wt w' (Rj M j (insert x S) w') ≤
      MatroidProphetKW.Single.wt w' (Rj M j (S ∪ U) w') -
        MatroidProphetKW.Single.wt w' (Rj M j (insert x (S ∪ U)) w') := by
  induction U using Finset.induction_on with
  | empty => intro _ _ _; simp
  | insert y U hyU ih =>
    intro hd hx hind
    rw [Finset.union_insert] at hx hind ⊢
    have hd' : Disjoint S U := Finset.disjoint_of_subset_right (Finset.subset_insert _ _) hd
    have hyS : y ∉ S := fun h => Finset.disjoint_left.1 hd h (Finset.mem_insert_self _ _)
    have hxy : x ≠ y := fun h => hx (h ▸ Finset.mem_insert_self _ _)
    have hx' : x ∉ S ∪ U := fun h => hx (Finset.mem_insert_of_mem h)
    have hyT : y ∉ S ∪ U := by
      rw [Finset.mem_union]; rintro (h | h); exacts [hyS h, hyU h]
    have hind' : (M j).Indep (↑(insert x (S ∪ U)) : Set α) := hind.subset (by
      intro z; simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe,
        Finset.mem_union]; tauto)
    have h1 := ih hd' hx' hind'
    have h2 := pv34_submod M hE j w' hw (S ∪ U) x y hxy hx' hyT hind
    linarith

theorem pv34_marg {p : ℕ} (M : Fin p → Matroid α) (hE : ∀ j, (M j).E = Set.univ)
    (j : Fin p) (w' : α → ℝ) (hw : ∀ x, 0 ≤ w' x) (S T : Finset α) (x : α) (hST : S ⊆ T)
    (hx : x ∉ T) (hind : (M j).Indep (↑(insert x T) : Set α)) :
    MatroidProphetKW.Single.wt w' (Rj M j S w') -
        MatroidProphetKW.Single.wt w' (Rj M j (insert x S) w') ≤
      MatroidProphetKW.Single.wt w' (Rj M j T w') -
        MatroidProphetKW.Single.wt w' (Rj M j (insert x T) w') := by
  have e : S ∪ (T \ S) = T := Finset.union_sdiff_of_subset hST
  have := pv34_marg_union M hE j w' hw S x (T \ S) Finset.disjoint_sdiff (by rw [e]; exact hx)
    (by rw [e]; exact hind)
  rwa [e] at this

theorem pv34_notMem_take (xs : List α) (hnd : xs.Nodup) (i : ℕ) (hi : i < xs.length) :
    xs[i] ∉ xs.take i := by
  intro h
  obtain ⟨k, hk, hke⟩ := List.getElem_of_mem h
  rw [List.getElem_take] at hke
  have hk' : k < i := by rw [List.length_take] at hk; omega
  have := (hnd.getElem_inj_iff).1 hke
  omega

theorem pv34_take_succ (xs : List α) (i : ℕ) (hi : i < xs.length) :
    (xs.take (i + 1)).toFinset = insert xs[i] (xs.take i).toFinset := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi]
  ext z
  simp only [Option.toList_some, List.toFinset_append, Finset.mem_union, List.mem_toFinset,
    List.toFinset_cons, List.toFinset_nil, Finset.mem_insert, Finset.notMem_empty]
  try simp only [insert_empty_eq, Finset.mem_singleton]
  try tauto

/-- Proposition 2 (per matroid, pointwise in `w′ ≥ 0`), for any prefix sets `S i ⊆ A`. -/
theorem pv34_prop2 {p : ℕ} (M : Fin p → Matroid α) (hE : ∀ j, (M j).E = Set.univ)
    (j : Fin p) (xs : List α) (hnd : xs.Nodup) (A V : Finset α) (hAV : Disjoint A V)
    (hInd : (M j).Indep (↑(A ∪ V) : Set α)) (w' : α → ℝ) (hw : ∀ x, 0 ≤ w' x)
    (S : ℕ → Finset α) (hS : ∀ i : Fin xs.length, S i ⊆ A) :
    sumOn xs V (fun i => MatroidProphetKW.Single.wt w' (Rj M j (S i) w') -
        MatroidProphetKW.Single.wt w' (Rj M j (insert xs[i] (S i)) w')) ≤
      MatroidProphetKW.Single.wt w' (Rj M j A w') := by
  classical
  let h : ℕ → ℝ := fun k =>
    MatroidProphetKW.Single.wt w' (Rj M j (A ∪ (V ∩ (xs.take k).toFinset)) w')
  have hstep : ∀ i : Fin xs.length,
      (if xs[i] ∈ V then MatroidProphetKW.Single.wt w' (Rj M j (S i) w') -
        MatroidProphetKW.Single.wt w' (Rj M j (insert xs[i] (S i)) w') else 0) ≤
        h i - h (i + 1) := by
    intro i
    have ht := pv34_take_succ xs i i.2
    by_cases hv : xs[i] ∈ V
    · rw [if_pos hv]
      have e : A ∪ (V ∩ (xs.take (i + 1)).toFinset) =
          insert xs[i] (A ∪ (V ∩ (xs.take i).toFinset)) := by
        have hv' : xs[(i : ℕ)] ∈ V := hv
        rw [ht]; ext z; by_cases hz : z = xs[(i : ℕ)]
        · subst hz; simp [hv']
        · simp [hz]
      show _ ≤ MatroidProphetKW.Single.wt w' (Rj M j (A ∪ (V ∩ (xs.take i).toFinset)) w') -
        MatroidProphetKW.Single.wt w' (Rj M j (A ∪ (V ∩ (xs.take (i + 1)).toFinset)) w')
      rw [e]
      have hxA : xs[i] ∉ A := fun h' => Finset.disjoint_left.1 hAV h' hv
      have hxT : xs[i] ∉ A ∪ (V ∩ (xs.take i).toFinset) := by
        rw [Finset.mem_union, Finset.mem_inter, List.mem_toFinset]
        rintro (h' | h')
        · exact hxA h'
        · exact pv34_notMem_take xs hnd i i.2 h'.2
      refine pv34_marg M hE j w' hw _ _ _ ((hS i).trans Finset.subset_union_left) hxT ?_
      refine hInd.subset ?_
      intro z
      simp only [Finset.coe_insert, Finset.coe_union, Finset.coe_inter, Set.mem_insert_iff,
        Set.mem_union, Set.mem_inter_iff, Finset.mem_coe]
      rintro (rfl | h' | h')
      · exact Or.inr hv
      · exact Or.inl h'
      · exact Or.inr h'.1
    · rw [if_neg hv]
      have e : V ∩ (xs.take (i + 1)).toFinset = V ∩ (xs.take i).toFinset := by
        have hv' : xs[(i : ℕ)] ∉ V := hv
        rw [ht]; ext z; by_cases hz : z = xs[(i : ℕ)]
        · subst hz; simp [hv']
        · simp [hz]
      show (0 : ℝ) ≤ MatroidProphetKW.Single.wt w' (Rj M j (A ∪ (V ∩ (xs.take i).toFinset)) w') -
        MatroidProphetKW.Single.wt w' (Rj M j (A ∪ (V ∩ (xs.take (i + 1)).toFinset)) w')
      rw [e, sub_self]
  have hsum : sumOn xs V (fun i => MatroidProphetKW.Single.wt w' (Rj M j (S i) w') -
        MatroidProphetKW.Single.wt w' (Rj M j (insert xs[i] (S i)) w')) ≤ h 0 - h xs.length := by
    unfold sumOn
    calc _ ≤ ∑ i : Fin xs.length, (h i - h (i + 1)) := Finset.sum_le_sum fun i _ => hstep i
      _ = ∑ i ∈ Finset.range xs.length, (h i - h (i + 1)) :=
          Fin.sum_univ_eq_sum_range (fun i => h i - h (i + 1)) xs.length
      _ = h 0 - h xs.length := Finset.sum_range_sub' h xs.length
  have h0 : h 0 = MatroidProphetKW.Single.wt w' (Rj M j A w') := by
    show MatroidProphetKW.Single.wt w' (Rj M j (A ∪ (V ∩ (xs.take 0).toFinset)) w') = _
    simp
  have hn : 0 ≤ h xs.length := Finset.sum_nonneg fun x _ => hw x
  linarith

theorem pv34_int_sumOn (μ : Measure (α → ℝ)) (xs : List α) (V : Finset α)
    (g : Fin xs.length → (α → ℝ) → ℝ) (hg : ∀ i, Integrable (g i) μ) :
    Integrable (fun w' => sumOn xs V (fun i => g i w')) μ ∧
      ∫ w', sumOn xs V (fun i => g i w') ∂μ = sumOn xs V (fun i => ∫ w', g i w' ∂μ) := by
  refine ⟨?_, ?_⟩
  · unfold sumOn
    refine integrable_finsetSum _ (fun i _ => ?_)
    split_ifs
    · exact hg i
    · exact integrable_zero _ _ _
  · unfold sumOn
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs
      · rfl
      · exact integral_zero _ _
    · intro i _
      split_ifs
      · exact hg i
      · exact integrable_zero _ _ _

end Infra

open MeasureTheory MatroidProphetKW.Inter in
theorem solution
    {α : Type*} [Fintype α] [DecidableEq α] {p : ℕ}
    (M : Fin p → Matroid α) (hE : ∀ j, (M j).E = Set.univ)
    (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)]
    (hF_nonneg : ∀ x, F x (Set.Iio 0) = 0) (hF_int : ∀ x, Integrable id (F x))
    (a : ℝ) (ha : 0 < a) :
    Balanced14 M F a (sumRule M F a) := by
  intro xs hnd hall w hw V hdisj hind
  let S : ℕ → Finset α := fun i => sel (sumRule M F a) M xs w i
  have hS : ∀ i : Fin xs.length, S i ⊆ selected (sumRule M F a) M xs w :=
    fun i => pvf1_sel_mono _ M xs w (le_of_lt i.2)
  have hint : ∀ (j : Fin p) (T : Finset α),
      Integrable (fun w' => MatroidProphetKW.Single.wt w' (Rj M j T w')) (law F) :=
    fun j T => pvf1_int_wtD F hF_int _ (pvf1_Rj_ms M j T)
  have hd : ∀ (j : Fin p) (i : Fin xs.length), Integrable (fun w' =>
      MatroidProphetKW.Single.wt w' (Rj M j (S i) w') -
        MatroidProphetKW.Single.wt w' (Rj M j (insert xs[i] (S i)) w')) (law F) :=
    fun j i => (hint j _).sub (hint j _)
  have key : sumOn xs V (thrAt (sumRule M F a) M xs w) =
      (1 / a) * ∑ j, sumOn xs V (fun i => ∫ w',
        (MatroidProphetKW.Single.wt w' (Rj M j (S i) w') -
          MatroidProphetKW.Single.wt w' (Rj M j (insert xs[i] (S i)) w')) ∂(law F)) := by
    unfold sumOn
    rw [Finset.mul_sum]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hc : xs[i] ∈ V
    · simp only [if_pos hc]
      rfl
    · simp only [if_neg hc, mul_zero, Finset.sum_const_zero]
  have hj : ∀ j : Fin p, sumOn xs V (fun i => ∫ w',
        (MatroidProphetKW.Single.wt w' (Rj M j (S i) w') -
          MatroidProphetKW.Single.wt w' (Rj M j (insert xs[i] (S i)) w')) ∂(law F)) =
      ∫ w', sumOn xs V (fun i =>
        MatroidProphetKW.Single.wt w' (Rj M j (S i) w') -
          MatroidProphetKW.Single.wt w' (Rj M j (insert xs[i] (S i)) w')) ∂(law F) :=
    fun j => ((pv34_int_sumOn (law F) xs V _ (hd j)).2).symm
  rw [key, Finset.sum_congr rfl fun j _ => hj j,
    ← integral_finsetSum _ (fun j _ => (pv34_int_sumOn (law F) xs V _ (hd j)).1)]
  refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (one_div_pos.2 ha))
  refine integral_mono_ae (integrable_finsetSum _ (fun j _ => (pv34_int_sumOn (law F) xs V _ (hd j)).1))
    (integrable_finsetSum _ (fun j _ => hint j _)) ?_
  filter_upwards [pvf1_ae_nonneg F hF_nonneg] with w' hw'
  exact Finset.sum_le_sum fun j _ =>
    pv34_prop2 M hE j xs hnd _ V hdisj (hind j) w' hw' S hS
