-- Prove2me | solution 1 for MatroidProphetKW.Inter.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T19:37:34.228185+00:00
-- url     : https://prove2.me/submissions/1b351ad5-ebfe-4edd-b748-e97df72e57da

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

theorem pvf1_iter_ms (adv : Adversary α) (k : ℕ) (l : List α) :
    MeasurableSet {w : α → ℝ | (fun xs => xs ++ [adv.next xs w])^[k] [] = l} := by
  induction k generalizing l with
  | zero => simp only [Function.iterate_zero, id_eq]; exact MeasurableSet.const _
  | succ k ih =>
    simp only [Function.iterate_succ_apply']
    exact pvf1_ms_comp (fun w => (fun xs => xs ++ [adv.next xs w])^[k] []) ih
      (fun l' w => l' ++ [adv.next l' w]) {l}
      (fun l' => pvf1_ms_of_disc (fun w => adv.next l' w) (fun x => adv.meas l' x)
        {x | l' ++ [x] = l})

theorem pvf1_rev_ms (adv : Adversary α) (l : List α) :
    MeasurableSet {w : α → ℝ | revealOrder adv w = l} :=
  pvf1_iter_ms adv _ l

theorem pvf1_sel_ms {p : ℕ} (rule : ThresholdRule α) (M : Fin p → Matroid α) (xs : List α)
    (i : ℕ) (S : Finset α) : MeasurableSet {w : α → ℝ | sel rule M xs w i = S} := by
  induction i generalizing S with
  | zero => simp only [sel]; exact MeasurableSet.const _
  | succ i ih =>
    by_cases h : i < xs.length
    · simp only [sel, dif_pos h]
      refine pvf1_ms_comp (fun w => sel rule M xs w i) ih
        (fun S' w => by
          classical
          exact if IsIndep M (insert xs[i] S') ∧ rule.thr S' (xs.take i) w xs[i] ≤ w xs[i]
            then insert xs[i] S' else S') {S} (fun S' => ?_)
      convert pvf1_ms_ite (fun w => IsIndep M (insert xs[i] S') ∧
          rule.thr S' (xs.take i) w xs[i] ≤ w xs[i]) ?_ (insert xs[i] S') S' {S} using 0
      exact (MeasurableSet.const _).inter (measurableSet_le (rule.meas _ _ _) (measurable_pi_apply _))
    · simp only [sel, dif_neg h]
      exact ih S

theorem pvf1_selected_ms {p : ℕ} (rule : ThresholdRule α) (M : Fin p → Matroid α)
    (xs : List α) (S : Finset α) : MeasurableSet {w : α → ℝ | selected rule M xs w = S} :=
  pvf1_sel_ms rule M xs _ S

theorem pvf1_adSel_ms {p : ℕ} (rule : ThresholdRule α) (M : Fin p → Matroid α)
    (adv : Adversary α) (S : Finset α) :
    MeasurableSet {w : α → ℝ | adaptiveSelected rule M adv w = S} :=
  pvf1_dm_comp (revealOrder adv) (pvf1_rev_ms adv) (fun l w => selected rule M l w)
    (fun l S => pvf1_selected_ms rule M l S) S

theorem pvf1_thrAt_meas {p : ℕ} (rule : ThresholdRule α) (M : Fin p → Matroid α)
    (xs : List α) (i : Fin xs.length) : Measurable (fun w => thrAt rule M xs w i) :=
  pvf1_meas_comp (fun w => sel rule M xs w i) (pvf1_sel_ms rule M xs i)
    (fun S w => rule.thr S (xs.take i) w xs[i]) (fun S => rule.meas _ _ _)

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

theorem pvf1_Rfam_ms {p : ℕ} (M : Fin p → Matroid α) (A : Finset α) (g : Fin p → Finset α) :
    MeasurableSet {w : α → ℝ | (fun j => Rj M j A w) = g} := by
  have : {w : α → ℝ | (fun j => Rj M j A w) = g} = ⋂ j, {w | Rj M j A w = g j} := by
    ext w; simp [funext_iff]
  rw [this]
  exact MeasurableSet.iInter fun j => pvf1_Rj_ms M j A (g j)

theorem pvf1_Rint_ms {p : ℕ} (M : Fin p → Matroid α) (A S0 : Finset α) :
    MeasurableSet {w : α → ℝ | Rint M A w = S0} := by
  have : ∀ w, Rint M A w =
      (fun g : Fin p → Finset α => Finset.univ.filter (fun x => ∀ j, x ∈ g j))
        (fun j => Rj M j A w) := fun w => rfl
  simp only [this]
  exact pvf1_dm_comp (fun w => fun j => Rj M j A w) (pvf1_Rfam_ms M A)
    (fun g _ => Finset.univ.filter (fun x => ∀ j, x ∈ g j))
    (fun _ _ => MeasurableSet.const _) S0

theorem pvf1_Cj_ms {p : ℕ} (M : Fin p → Matroid α) (j : Fin p) (A S0 : Finset α) :
    MeasurableSet {w : α → ℝ | Cj M j A w = S0} := by
  have : {w : α → ℝ | Cj M j A w = S0} = {w | (B M w, Rj M j A w) ∈ {q | q.1 \ q.2 = S0}} := rfl
  rw [this]
  refine pvf1_ms_of_disc (fun w => (B M w, Rj M j A w)) (fun q => ?_) _
  have : {w : α → ℝ | (B M w, Rj M j A w) = q} = {w | B M w = q.1} ∩ {w | Rj M j A w = q.2} := by
    ext w; simp [Prod.ext_iff]
  rw [this]
  exact (pvf1_B_ms M q.1).inter (pvf1_Rj_ms M j A q.2)

theorem pvf1_Cint_ms {p : ℕ} (M : Fin p → Matroid α) (A S0 : Finset α) :
    MeasurableSet {w : α → ℝ | Cint M A w = S0} := by
  have : ∀ w, Cint M A w =
      (fun q : Finset α × (Fin p → Finset α) => Finset.univ.biUnion (fun j => q.1 \ q.2 j))
        (B M w, fun j => Rj M j A w) := fun w => rfl
  simp only [this]
  refine pvf1_dm_comp (fun w => (B M w, fun j => Rj M j A w)) (fun q => ?_)
    (fun (q : Finset α × (Fin p → Finset α)) _ => Finset.univ.biUnion (fun j => q.1 \ q.2 j))
    (fun _ _ => MeasurableSet.const _) S0
  have : {w : α → ℝ | (B M w, fun j => Rj M j A w) = q} =
      {w | B M w = q.1} ∩ {w | (fun j => Rj M j A w) = q.2} := by
    ext w; simp [Prod.ext_iff]
  rw [this]
  exact (pvf1_B_ms M q.1).inter (pvf1_Rfam_ms M A q.2)

/-- splitting off one coordinate of the product law (lintegral form) -/
theorem pvf1_lint_update (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)] (x : α)
    (f : (α → ℝ) → ENNReal) (hf : Measurable f) :
    ∫⁻ w, f w ∂(law F) = ∫⁻ w, ∫⁻ t, f (Function.update w x t) ∂(F x) ∂(law F) := by
  have hg : Measurable (fun w : α → ℝ => ∫⁻ t, f (Function.update w x t) ∂(F x)) := by
    have := Measurable.lmarginal F (s := {x}) hf
    rwa [lmarginal_singleton] at this
  have huniv : (Finset.univ : Finset α) = insert x (Finset.univ.erase x) := by
    rw [Finset.insert_erase (Finset.mem_univ x)]
  have hx : x ∉ Finset.univ.erase x := Finset.notMem_erase x _
  unfold law
  rw [lintegral_eq_lmarginal_univ (0 : α → ℝ), lintegral_eq_lmarginal_univ (0 : α → ℝ), huniv,
    lmarginal_insert' _ hf hx, lmarginal_insert' _ hg hx]
  congr 1
  funext w
  simp only [Function.update_idem]
  rw [lintegral_const, measure_univ, mul_one]

end Infra

section Struct

open MatroidProphetKW.Inter

variable {α : Type*} [Fintype α] [DecidableEq α]

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

/-- `A ∪ R_j(A)` is `M j`-independent unless `R_j(A) = ∅`. -/
theorem pvf1_Rj_indep {p : ℕ} (M : Fin p → Matroid α) (j : Fin p) (A : Finset α)
    (w' : α → ℝ) : (M j).Indep (↑(A ∪ Rj M j A w') : Set α) ∨ Rj M j A w' = ∅ := by
  unfold Rj
  by_cases h : ∃ R, R ⊆ B M w' \ A ∧ (M j).Indep (↑(A ∪ R) : Set α) ∧
      (↑(B M w') : Set α) ⊆ (M j).closure (↑(A ∪ R) : Set α)
  · exact Or.inl (pvf1_argmaxOn_spec _ (MatroidProphetKW.Single.wt w') h).1.2.1
  · exact Or.inr (pvf1_argmaxOn_empty _ _ h)

theorem pvf1_Rj_disj {p : ℕ} (M : Fin p → Matroid α) (j : Fin p) (A : Finset α)
    (w' : α → ℝ) : Disjoint A (Rj M j A w') := by
  unfold Rj
  by_cases h : ∃ R, R ⊆ B M w' \ A ∧ (M j).Indep (↑(A ∪ R) : Set α) ∧
      (↑(B M w') : Set α) ⊆ (M j).closure (↑(A ∪ R) : Set α)
  · have := (pvf1_argmaxOn_spec _ (MatroidProphetKW.Single.wt w') h).1.1
    exact Finset.disjoint_of_subset_right this Finset.disjoint_sdiff
  · rw [pvf1_argmaxOn_empty _ _ h]; exact Finset.disjoint_empty_right _

theorem pvf1_Rint_sub_Rj {p : ℕ} (M : Fin p → Matroid α) (j : Fin p) (A : Finset α)
    (w' : α → ℝ) : Rint M A w' ⊆ Rj M j A w' := by
  intro x hx
  exact (Finset.mem_filter.1 hx).2 j

/-- `A ∪ R(A) ∈ ℐ` for feasible `A`. -/
theorem pvf1_Rint_indep {p : ℕ} (M : Fin p → Matroid α) (A : Finset α) (hA : IsIndep M A)
    (w' : α → ℝ) : IsIndep M (A ∪ Rint M A w') := by
  intro j
  rcases pvf1_Rj_indep M j A w' with h | h
  · apply h.subset
    exact_mod_cast Finset.union_subset_union (le_refl A) (pvf1_Rint_sub_Rj M j A w')
  · have h0 : Rint M A w' = ∅ := Finset.subset_empty.1 (h ▸ pvf1_Rint_sub_Rj M j A w')
    rw [h0, Finset.union_empty]
    exact hA j

theorem pvf1_Rint_disj {p : ℕ} (hp : 0 < p) (M : Fin p → Matroid α) (A : Finset α)
    (w' : α → ℝ) : Disjoint A (Rint M A w') :=
  Finset.disjoint_of_subset_right (pvf1_Rint_sub_Rj M ⟨0, hp⟩ A w') (pvf1_Rj_disj M _ A w')

theorem pvf1_Rint_sub_B {p : ℕ} (hp : 0 < p) (M : Fin p → Matroid α) (A : Finset α)
    (w' : α → ℝ) : Rint M A w' ⊆ B M w' :=
  (pvf1_Rint_sub_Rj M ⟨0, hp⟩ A w').trans (pvf1_Rj_sub_B M _ A w')

theorem pvf1_Cint_eq {p : ℕ} (M : Fin p → Matroid α) (A : Finset α) (w' : α → ℝ) :
    Cint M A w' = B M w' \ Rint M A w' := by
  ext x
  simp only [Cint, Cj, Rint, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_sdiff,
    Finset.mem_filter, not_forall]
  constructor
  · rintro ⟨j, hB, hj⟩; exact ⟨hB, j, hj⟩
  · rintro ⟨hB, j, hj⟩; exact ⟨j, hB, hj⟩

theorem pvf1_eq20 {p : ℕ} (M : Fin p → Matroid α) (j : Fin p) (A : Finset α) (w' : α → ℝ) :
    MatroidProphetKW.Single.wt w' (Cj M j A w') + MatroidProphetKW.Single.wt w' (Rj M j A w')
      = OPT M w' := by
  rw [pvf1_OPT_eq]
  unfold Cj MatroidProphetKW.Single.wt
  exact Finset.sum_sdiff (pvf1_Rj_sub_B M j A w')

theorem pvf1_eq21 {p : ℕ} (hp : 0 < p) (M : Fin p → Matroid α) (A : Finset α) (w' : α → ℝ) :
    MatroidProphetKW.Single.wt w' (Cint M A w') + MatroidProphetKW.Single.wt w' (Rint M A w')
      = OPT M w' := by
  rw [pvf1_OPT_eq, pvf1_Cint_eq]
  unfold MatroidProphetKW.Single.wt
  exact Finset.sum_sdiff (pvf1_Rint_sub_B hp M A w')

theorem pvf1_wt_biUnion_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (C : ι → Finset α)
    (w : α → ℝ) (hw : ∀ x, 0 ≤ w x) :
    MatroidProphetKW.Single.wt w (s.biUnion C) ≤ ∑ j ∈ s, MatroidProphetKW.Single.wt w (C j) := by
  induction s using Finset.induction_on with
  | empty => simp [MatroidProphetKW.Single.wt]
  | insert j s hj ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hj]
    have h := Finset.sum_union_inter (s₁ := C j) (s₂ := s.biUnion C) (f := w)
    have h2 : 0 ≤ ∑ x ∈ C j ∩ s.biUnion C, w x := Finset.sum_nonneg fun x _ => hw x
    unfold MatroidProphetKW.Single.wt at ih ⊢
    linarith

/-- (21) with the union bound: `w'(R(A)) ≥ OPT(w') − ∑_j w'(C_j(A))` for `w' ≥ 0`. -/
theorem pvf1_Rint_ge {p : ℕ} (hp : 0 < p) (M : Fin p → Matroid α) (A : Finset α) (w' : α → ℝ)
    (hw : ∀ x, 0 ≤ w' x) :
    OPT M w' - ∑ j, MatroidProphetKW.Single.wt w' (Cj M j A w') ≤
      MatroidProphetKW.Single.wt w' (Rint M A w') := by
  have h1 := pvf1_eq21 hp M A w'
  have h2 := pvf1_wt_biUnion_le Finset.univ (fun j => Cj M j A w') w' hw
  have h3 : Cint M A w' = Finset.univ.biUnion (fun j => Cj M j A w') := rfl
  rw [← h3] at h2
  linarith

/-! ### the selection process -/

theorem pvf1_sel_indep {p : ℕ} (rule : ThresholdRule α) (M : Fin p → Matroid α) (xs : List α)
    (w : α → ℝ) (k : ℕ) : IsIndep M (sel rule M xs w k) := by
  induction k with
  | zero => intro j; simp [sel]
  | succ k ih =>
    simp only [sel]
    split_ifs with h1 h2
    · exact h2.1
    · exact ih
    · exact ih

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

theorem pvf1_cond_mem {p : ℕ} (rule : ThresholdRule α) (M : Fin p → Matroid α)
    (xs : List α) (w : α → ℝ) (i : ℕ) (h : i < xs.length)
    (hc : IsIndep M (insert xs[i] (sel rule M xs w i)) ∧
      rule.thr (sel rule M xs w i) (xs.take i) w xs[i] ≤ w xs[i]) :
    xs[i] ∈ sel rule M xs w (i + 1) := by
  simp only [sel, dif_pos h, if_pos hc]
  exact Finset.mem_insert_self _ _

/-- For a duplicate-free order, `x_i ∈ A` iff step `i` accepted. -/
theorem pvf1_mem_selected_iff {p : ℕ} (rule : ThresholdRule α) (M : Fin p → Matroid α)
    (xs : List α) (hnd : xs.Nodup) (w : α → ℝ) (i : Fin xs.length) :
    xs[i] ∈ selected rule M xs w ↔
      (IsIndep M (insert xs[i] (sel rule M xs w i)) ∧ thrAt rule M xs w i ≤ w xs[i]) := by
  constructor
  · intro hx
    obtain ⟨i', h', -, heq, hc⟩ := pvf1_mem_sel rule M xs w _ _ hx
    have : i' = (i : ℕ) := (hnd.getElem_inj_iff).1 heq
    subst this
    exact hc
  · intro hc
    exact pvf1_sel_mono rule M xs w (Nat.succ_le_of_lt i.2) (pvf1_cond_mem rule M xs w i i.2 hc)

theorem pvf1_iter_props (adv : Adversary α) (w : α → ℝ) (k : ℕ) (hk : k ≤ Fintype.card α) :
    ((fun xs => xs ++ [adv.next xs w])^[k] []).Nodup ∧
      ((fun xs => xs ++ [adv.next xs w])^[k] []).length = k := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨hnd, hlen⟩ := ih (by omega)
    rw [Function.iterate_succ_apply']
    set L := (fun xs => xs ++ [adv.next xs w])^[k] [] with hL
    have hex : ∃ y, y ∉ L := by
      by_contra hcon
      push_neg at hcon
      have hsub : (Finset.univ : Finset α) ⊆ L.toFinset := fun y _ => List.mem_toFinset.2 (hcon y)
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_univ, List.toFinset_card_of_nodup hnd, hlen] at h1
      omega
    have hfresh := adv.fresh L w hex
    refine ⟨List.nodup_append.2 ⟨hnd, List.nodup_singleton _, ?_⟩, by simp [hlen]⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb
    subst hb
    rintro rfl
    exact hfresh ha

theorem pvf1_rev_nodup (adv : Adversary α) (w : α → ℝ) : (revealOrder adv w).Nodup :=
  (pvf1_iter_props adv w _ le_rfl).1

theorem pvf1_rev_len (adv : Adversary α) (w : α → ℝ) :
    (revealOrder adv w).length = Fintype.card α :=
  (pvf1_iter_props adv w _ le_rfl).2

theorem pvf1_rev_all (adv : Adversary α) (w : α → ℝ) (x : α) : x ∈ revealOrder adv w := by
  have h1 : (revealOrder adv w).toFinset = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [List.toFinset_card_of_nodup (pvf1_rev_nodup adv w), pvf1_rev_len]
  have : x ∈ (revealOrder adv w).toFinset := by rw [h1]; exact Finset.mem_univ x
  exact List.mem_toFinset.1 this

theorem pvf1_sumOn_eq (xs : List α) (hnd : xs.Nodup) (hall : ∀ x, x ∈ xs) (S : Finset α)
    (g : α → ℝ) : sumOn xs S (fun i => g xs[i]) = ∑ x ∈ S, g x := by
  unfold sumOn
  show (∑ i : Fin xs.length, if xs[i] ∈ S then g xs[i] else 0) = _
  rw [Fintype.sum_equiv (List.Nodup.getEquivOfForallMemList xs hnd hall) _
    (fun x => if x ∈ S then g x else 0) (fun i => by
      simp only [List.Nodup.getEquivOfForallMemList_apply, List.get_eq_getElem]
      split_ifs <;> first | rfl | contradiction)]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- (22), pointwise: `w(A) = ∑_{x_i∈A} T_i + ∑_{x_i∈A} (w_i − T_i)^+`. -/
theorem pvf1_eq22 {p : ℕ} (rule : ThresholdRule α) (M : Fin p → Matroid α)
    (xs : List α) (hnd : xs.Nodup) (hall : ∀ x, x ∈ xs) (w : α → ℝ) :
    MatroidProphetKW.Single.wt w (selected rule M xs w) =
      sumOn xs (selected rule M xs w) (thrAt rule M xs w) +
      sumOn xs (selected rule M xs w) (fun i => max (w xs[i] - thrAt rule M xs w i) 0) := by
  have h1 : MatroidProphetKW.Single.wt w (selected rule M xs w) =
      sumOn xs (selected rule M xs w) (fun i => w xs[i]) :=
    (pvf1_sumOn_eq xs hnd hall _ w).symm
  rw [h1]
  unfold sumOn
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : xs[i] ∈ selected rule M xs w
  · rw [if_pos hi, if_pos hi, if_pos hi]
    have := ((pvf1_mem_selected_iff rule M xs hnd w i).1 hi).2
    show w xs[i] = thrAt rule M xs w i + max (w xs[i] - thrAt rule M xs w i) 0
    rw [max_eq_left (by linarith)]
    ring
  · rw [if_neg hi, if_neg hi, if_neg hi, add_zero]

end Struct

section Integ

open MatroidProphetKW.Inter

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem pvf1_ae_nonneg (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)]
    (hF_nonneg : ∀ x, F x (Set.Iio 0) = 0) : ∀ᵐ w' ∂(law F), ∀ y, 0 ≤ w' y := by
  rw [ae_all_iff]
  intro y
  rw [ae_iff]
  have hset : {a : α → ℝ | ¬ 0 ≤ a y} = Function.eval y ⁻¹' Set.Iio 0 := by
    ext a; simp
  rw [hset]
  exact Measure.pi_eval_preimage_null F (hF_nonneg y)

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

/-- a function of the selected set is integrable (finite range). -/
theorem pvf1_int_ofA {p : ℕ} (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)]
    (rule : ThresholdRule α) (M : Fin p → Matroid α) (adv : Adversary α) (k : Finset α → ℝ) :
    Integrable (fun w => k (adaptiveSelected rule M adv w)) (law F) := by
  haveI : IsProbabilityMeasure (law F) := by unfold law; infer_instance
  have hm : Measurable (fun w => k (adaptiveSelected rule M adv w)) :=
    pvf1_meas_comp (adaptiveSelected rule M adv) (pvf1_adSel_ms rule M adv)
      (fun S _ => k S) (fun _ => measurable_const)
  refine Integrable.of_bound hm.aestronglyMeasurable (∑ S : Finset α, |k S|)
    (ae_of_all _ fun w => ?_)
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun S => |k S|) (fun S _ => abs_nonneg _)
    (Finset.mem_univ _)

theorem pvf1_sumOnA_meas {p : ℕ} (rule : ThresholdRule α) (M : Fin p → Matroid α)
    (adv : Adversary α) (g : (l : List α) → (α → ℝ) → Fin l.length → ℝ)
    (hg : ∀ l i, Measurable (fun w => g l w i)) :
    Measurable (fun w => sumOn (revealOrder adv w) (adaptiveSelected rule M adv w)
      (g (revealOrder adv w) w)) := by
  refine pvf1_meas_comp (revealOrder adv) (pvf1_rev_ms adv)
    (fun l w => sumOn l (selected rule M l w) (g l w)) (fun l => ?_)
  unfold sumOn
  exact Finset.measurable_sum _ (fun i _ => Measurable.ite
    (pvf1_ms_of_disc (selected rule M l) (pvf1_selected_ms rule M l) {S | l[i] ∈ S})
    (hg l i) measurable_const)

theorem pvf1_sumOn_nonneg (xs : List α) (S : Finset α) (g : Fin xs.length → ℝ)
    (hg : ∀ i, 0 ≤ g i) : 0 ≤ sumOn xs S g := by
  unfold sumOn
  exact Finset.sum_nonneg fun i _ => by split_ifs; exacts [hg i, le_rfl]

/-- Assembly of Proposition 3 from (13), (23), (24), (20)-(21) and (22). -/
theorem pvf1_assembly {p : ℕ} (hp : 0 < p) (M : Fin p → Matroid α)
    (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)]
    (hF_nonneg : ∀ x, F x (Set.Iio 0) = 0) (hF_int : ∀ x, Integrable id (F x))
    (a : ℝ) (ha : 2 ≤ a) (rule : ThresholdRule α) (hthr : ∀ A xs w x, 0 ≤ rule.thr A xs w x)
    (h13 : Balanced13 M F a rule) (adv : Adversary α)
    (H23 : ∫ w, ∫ w', sumOn (revealOrder adv w) (Rint M (adaptiveSelected rule M adv w) w')
        (fun i => max (w' (revealOrder adv w)[i] - thrAt rule M (revealOrder adv w) w i) 0)
        ∂(law F) ∂(law F) ≤
      ∫ w, sumOn (revealOrder adv w) (adaptiveSelected rule M adv w)
        (fun i => max (w (revealOrder adv w)[i] - thrAt rule M (revealOrder adv w) w i) 0)
        ∂(law F))
    (H24 : (∫ w, ∫ w', MatroidProphetKW.Single.wt w' (Rint M (adaptiveSelected rule M adv w) w')
          ∂(law F) ∂(law F)) -
        (1 / a) * ∫ w, ∫ w', ∑ j, MatroidProphetKW.Single.wt w'
          (Rj M j (adaptiveSelected rule M adv w) w') ∂(law F) ∂(law F) ≤
      ∫ w, ∫ w', sumOn (revealOrder adv w) (Rint M (adaptiveSelected rule M adv w) w')
        (fun i => max (w' (revealOrder adv w)[i] - thrAt rule M (revealOrder adv w) w i) 0)
        ∂(law F) ∂(law F)) :
    (a - p) / (a * (a - 1)) * ∫ w, OPT M w ∂(law F) ≤
      ∫ w, MatroidProphetKW.Single.wt w (adaptiveSelected rule M adv w) ∂(law F) := by
  haveI : IsProbabilityMeasure (law F) := by unfold law; infer_instance
  set A := adaptiveSelected rule M adv with hAdef
  set xs := revealOrder adv with hxs
  have hapos : 0 < a := by linarith
  have hnn := pvf1_ae_nonneg F hF_nonneg
  -- the two halves of (22)
  set f1 : (α → ℝ) → ℝ := fun w => sumOn (xs w) (A w) (thrAt rule M (xs w) w) with hf1
  set f2 : (α → ℝ) → ℝ := fun w => sumOn (xs w) (A w)
    (fun i => max (w (xs w)[i] - thrAt rule M (xs w) w i) 0) with hf2
  have h22 : ∀ w, MatroidProphetKW.Single.wt w (A w) = f1 w + f2 w := fun w =>
    pvf1_eq22 rule M (xs w) (pvf1_rev_nodup adv w) (pvf1_rev_all adv w) w
  have hf1nn : ∀ w, 0 ≤ f1 w := fun w =>
    pvf1_sumOn_nonneg _ _ _ (fun i => hthr _ _ _ _)
  have hf2nn : ∀ w, 0 ≤ f2 w := fun w =>
    pvf1_sumOn_nonneg _ _ _ (fun i => le_max_right _ _)
  have hf1m : Measurable f1 := pvf1_sumOnA_meas rule M adv (fun l w i => thrAt rule M l w i)
    (fun l i => pvf1_thrAt_meas rule M l i)
  have hf2m : Measurable f2 := pvf1_sumOnA_meas rule M adv
    (fun l w i => max (w l[i] - thrAt rule M l w i) 0)
    (fun l i => ((measurable_pi_apply _).sub (pvf1_thrAt_meas rule M l i)).max measurable_const)
  have hbd : ∀ w, MatroidProphetKW.Single.wt w (A w) ≤ ∑ x, |w x| := fun w =>
    (le_abs_self _).trans (pvf1_abs_wt_le w (A w))
  have hf1i : Integrable f1 (law F) := by
    refine (pvf1_int_absSum F hF_int).mono' hf1m.aestronglyMeasurable (ae_of_all _ fun w => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hf1nn w)]
    linarith [h22 w, hbd w, hf2nn w]
  have hf2i : Integrable f2 (law F) := by
    refine (pvf1_int_absSum F hF_int).mono' hf2m.aestronglyMeasurable (ae_of_all _ fun w => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hf2nn w)]
    linarith [h22 w, hbd w, hf1nn w]
  have hY : ∫ w, MatroidProphetKW.Single.wt w (A w) ∂(law F) =
      ∫ w, f1 w ∂(law F) + ∫ w, f2 w ∂(law F) := by
    rw [← integral_add hf1i hf2i]
    exact integral_congr_ae (ae_of_all _ h22)
  -- the ghost-sample functions of the selected set
  let kC : Finset α → ℝ := fun S => ∫ w', ∑ j, MatroidProphetKW.Single.wt w' (Cj M j S w') ∂(law F)
  let kR : Finset α → ℝ := fun S => ∫ w', ∑ j, MatroidProphetKW.Single.wt w' (Rj M j S w') ∂(law F)
  let kR' : Finset α → ℝ := fun S => ∫ w', MatroidProphetKW.Single.wt w' (Rint M S w') ∂(law F)
  have hiC : ∀ S, Integrable (fun w' => ∑ j, MatroidProphetKW.Single.wt w' (Cj M j S w')) (law F) :=
    fun S => integrable_finsetSum _ fun j _ => pvf1_int_wtD F hF_int _ (pvf1_Cj_ms M j S)
  have hiR : ∀ S, Integrable (fun w' => ∑ j, MatroidProphetKW.Single.wt w' (Rj M j S w')) (law F) :=
    fun S => integrable_finsetSum _ fun j _ => pvf1_int_wtD F hF_int _ (pvf1_Rj_ms M j S)
  have hiO : Integrable (fun w' => OPT M w') (law F) := by
    have : (fun w' => OPT M w') = fun w' => MatroidProphetKW.Single.wt w' (B M w') :=
      funext fun w' => pvf1_OPT_eq M w'
    rw [this]; exact pvf1_int_wtD F hF_int _ (pvf1_B_ms M)
  set O := ∫ w, OPT M w ∂(law F) with hO
  -- (20) integrated: kC S + kR S = p O
  have hCR : ∀ S, kC S + kR S = p * O := by
    intro S
    simp only [kC, kR]
    rw [← integral_add (hiC S) (hiR S), hO, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun w' => ?_)
    simp only
    rw [← Finset.sum_add_distrib]
    simp only [pvf1_eq20 M _ S w', Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  -- (21) integrated: kR' S ≥ O − kC S
  have hR' : ∀ S, O - kC S ≤ kR' S := by
    intro S
    simp only [kC, kR']
    rw [hO, ← integral_sub hiO (hiC S)]
    refine integral_mono_ae (hiO.sub (hiC S)) (pvf1_int_wtD F hF_int _ (pvf1_Rint_ms M S)) ?_
    filter_upwards [hnn] with w' hw'
    exact pvf1_Rint_ge hp M S w' hw'
  -- (13) integrated
  have h13i : (1 / a) * ∫ w, kC (A w) ∂(law F) ≤ ∫ w, f1 w ∂(law F) := by
    rw [← integral_const_mul]
    refine integral_mono_ae ((pvf1_int_ofA F rule M adv kC).const_mul _) hf1i ?_
    filter_upwards [hnn] with w hw
    exact h13 (xs w) (pvf1_rev_nodup adv w) (pvf1_rev_all adv w) w hw
  have hU0 : 0 ≤ ∫ w, f2 w ∂(law F) := integral_nonneg hf2nn
  have hXR : ∫ w, kC (A w) ∂(law F) + ∫ w, kR (A w) ∂(law F) = p * O := by
    rw [← integral_add (pvf1_int_ofA F rule M adv kC) (pvf1_int_ofA F rule M adv kR)]
    simp only [hCR]
    simp
  have hR'i : O - ∫ w, kC (A w) ∂(law F) ≤ ∫ w, kR' (A w) ∂(law F) := by
    have hint : Integrable (fun w => O - kC (A w)) (law F) :=
      (integrable_const O).sub (pvf1_int_ofA F rule M adv kC)
    have := integral_mono hint (pvf1_int_ofA F rule M adv kR') (fun w => hR' (A w))
    rw [integral_sub (integrable_const O) (pvf1_int_ofA F rule M adv kC)] at this
    simpa using this
  -- combine
  have H := H23
  have H' := H24
  change ∫ w, kR' (A w) ∂(law F) - (1 / a) * ∫ w, kR (A w) ∂(law F) ≤ _ at H'
  change _ ≤ ∫ w, f2 w ∂(law F) at H
  rw [hY]
  set X := ∫ w, kC (A w) ∂(law F)
  set R := ∫ w, kR (A w) ∂(law F)
  set R' := ∫ w, kR' (A w) ∂(law F)
  set S1 := ∫ w, f1 w ∂(law F)
  set U := ∫ w, f2 w ∂(law F)
  have hX : X ≤ a * S1 := by
    have := mul_le_mul_of_nonneg_left h13i hapos.le
    rwa [← mul_assoc, mul_one_div_cancel hapos.ne', one_mul] at this
  have hRe : R = p * O - X := by linarith
  have hmain : a * (S1 + U) ≥ a * S1 + a * O - a * X - (p * O - X) := by
    have h1 : S1 + U ≥ S1 + R' - (1 / a) * R := by linarith
    have h2 : a * (S1 + U) ≥ a * (S1 + R' - (1 / a) * R) := mul_le_mul_of_nonneg_left h1 hapos.le
    have h3 : a * (S1 + R' - (1 / a) * R) = a * S1 + a * R' - R := by
      field_simp
    rw [h3, hRe] at h2
    nlinarith [mul_le_mul_of_nonneg_left hR'i hapos.le]
  have ha1 : 0 < a - 1 := by linarith
  have hS1U : S1 ≤ S1 + U := by linarith
  have hfin : (a - p) * O ≤ a * (a - 1) * (S1 + U) := by
    have e1 : (a - 1) * X ≤ (a - 1) * (a * S1) := mul_le_mul_of_nonneg_left hX ha1.le
    have e2 : a * (a - 2) * S1 ≤ a * (a - 2) * (S1 + U) :=
      mul_le_mul_of_nonneg_left hS1U (mul_nonneg hapos.le (by linarith))
    nlinarith
  rw [div_mul_eq_mul_div, div_le_iff₀ (mul_pos hapos ha1)]
  linarith

end Integ

section Eq24

open MatroidProphetKW.Inter

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem pvf1_sumOn_le_abs (xs : List α) (hnd : xs.Nodup) (hall : ∀ x, x ∈ xs) (S : Finset α)
    (w' : α → ℝ) (T : Fin xs.length → ℝ) (hT : ∀ i, 0 ≤ T i) :
    sumOn xs S (fun i => max (w' xs[i] - T i) 0) ≤ ∑ x, |w' x| := by
  have h1 : sumOn xs S (fun i => max (w' xs[i] - T i) 0) ≤
      sumOn xs Finset.univ (fun i => |w' xs[i]|) := by
    unfold sumOn
    refine Finset.sum_le_sum fun i _ => ?_
    rw [if_pos (Finset.mem_univ _)]
    split_ifs
    · exact max_le (by linarith [le_abs_self (w' xs[i]), hT i]) (abs_nonneg _)
    · exact abs_nonneg _
  rw [pvf1_sumOn_eq xs hnd hall Finset.univ (fun x => |w' x|)] at h1
  exact h1

/-- the joint integrand of (23)/(24) is measurable on the product space -/
theorem pvf1_h_meas {p : ℕ} (rule : ThresholdRule α) (M : Fin p → Matroid α)
    (adv : Adversary α) :
    Measurable (fun ω : (α → ℝ) × (α → ℝ) =>
      sumOn (revealOrder adv ω.1) (Rint M (adaptiveSelected rule M adv ω.1) ω.2)
        (fun i => max (ω.2 (revealOrder adv ω.1)[i] -
          thrAt rule M (revealOrder adv ω.1) ω.1 i) 0)) := by
  refine pvf1_meas_comp (fun ω : (α → ℝ) × (α → ℝ) => revealOrder adv ω.1)
    (pvf1_dm_fst _ (pvf1_rev_ms adv))
    (fun l ω => sumOn l (Rint M (selected rule M l ω.1) ω.2)
      (fun i => max (ω.2 l[i] - thrAt rule M l ω.1 i) 0)) (fun l => ?_)
  have hR : ∀ T, MeasurableSet {ω : (α → ℝ) × (α → ℝ) | Rint M (selected rule M l ω.1) ω.2 = T} :=
    pvf1_dm_comp (fun ω : (α → ℝ) × (α → ℝ) => selected rule M l ω.1)
      (pvf1_dm_fst _ (pvf1_selected_ms rule M l)) (fun S ω => Rint M S ω.2)
      (fun S T => pvf1_dm_snd _ (pvf1_Rint_ms M S) T)
  unfold sumOn
  exact Finset.measurable_sum _ (fun i _ => Measurable.ite
    (pvf1_ms_of_disc _ hR {S | l[i] ∈ S})
    ((((measurable_pi_apply _).comp measurable_snd).sub
      ((pvf1_thrAt_meas rule M l i).comp measurable_fst)).max measurable_const)
    measurable_const)

theorem pvf1_eq24 {p : ℕ} (hp : 0 < p) (M : Fin p → Matroid α)
    (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)]
    (hF_nonneg : ∀ x, F x (Set.Iio 0) = 0) (hF_int : ∀ x, Integrable id (F x))
    (a : ℝ) (rule : ThresholdRule α) (hthr : ∀ A xs w x, 0 ≤ rule.thr A xs w x)
    (h14 : Balanced14 M F a rule) (adv : Adversary α) :
    (∫ w, ∫ w', MatroidProphetKW.Single.wt w' (Rint M (adaptiveSelected rule M adv w) w') ∂(law F) ∂(law F)) -
        (1 / a) * ∫ w, ∫ w', ∑ j, MatroidProphetKW.Single.wt w' (Rj M j (adaptiveSelected rule M adv w) w')
          ∂(law F) ∂(law F) ≤
      ∫ w, ∫ w', sumOn (revealOrder adv w) (Rint M (adaptiveSelected rule M adv w) w')
        (fun i => max (w' (revealOrder adv w)[i] - thrAt rule M (revealOrder adv w) w i) 0)
        ∂(law F) ∂(law F) := by
  haveI : IsProbabilityMeasure (law F) := by unfold law; infer_instance
  have hnn := pvf1_ae_nonneg F hF_nonneg
  set A := adaptiveSelected rule M adv with hAdef
  set xs := revealOrder adv with hxs
  let kR : Finset α → ℝ := fun S => ∫ w', ∑ j, MatroidProphetKW.Single.wt w' (Rj M j S w') ∂(law F)
  let kR' : Finset α → ℝ := fun S => ∫ w', MatroidProphetKW.Single.wt w' (Rint M S w') ∂(law F)
  let h : (α → ℝ) × (α → ℝ) → ℝ := fun ω => sumOn (xs ω.1) (Rint M (A ω.1) ω.2)
    (fun i => max (ω.2 (xs ω.1)[i] - thrAt rule M (xs ω.1) ω.1 i) 0)
  have hm : Measurable h := pvf1_h_meas rule M adv
  have hbd : ∀ ω, h ω ≤ ∑ x, |ω.2 x| := fun ω =>
    pvf1_sumOn_le_abs (xs ω.1) (pvf1_rev_nodup adv _) (pvf1_rev_all adv _) _ _ _
      (fun i => hthr _ _ _ _)
  have hnn_h : ∀ ω, 0 ≤ h ω := fun ω => pvf1_sumOn_nonneg _ _ _ (fun i => le_max_right _ _)
  have hint_h : ∀ w, Integrable (fun w' => h (w, w')) (law F) := by
    intro w
    refine (pvf1_int_absSum F hF_int).mono' (hm.comp measurable_prodMk_left).aestronglyMeasurable
      (ae_of_all _ fun w' => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn_h _)]
    exact hbd (w, w')
  set C := ∫ w', ∑ x, |w' x| ∂(law F) with hC
  have hH : Integrable (fun w => ∫ w', h (w, w') ∂(law F)) (law F) := by
    refine Integrable.of_bound
      (hm.stronglyMeasurable.integral_prod_right' (ν := law F)).aestronglyMeasurable C
      (ae_of_all _ fun w => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun w' => hnn_h _)]
    exact integral_mono (hint_h w) (pvf1_int_absSum F hF_int) (fun w' => hbd (w, w'))
  have hptw : ∀ᵐ w ∂(law F), kR' (A w) - (1 / a) * kR (A w) ≤ ∫ w', h (w, w') ∂(law F) := by
    filter_upwards [hnn] with w hw
    have hAi : IsIndep M (A w) := pvf1_sel_indep rule M _ w _
    have hpt : ∀ w', MatroidProphetKW.Single.wt w' (Rint M (A w) w') - (1 / a) * kR (A w)
        ≤ h (w, w') := by
      intro w'
      have h14w := h14 (xs w) (pvf1_rev_nodup adv w) (pvf1_rev_all adv w) w hw
        (Rint M (A w) w') (pvf1_Rint_disj hp M (A w) w') (pvf1_Rint_indep M (A w) hAi w')
      have hwt := pvf1_sumOn_eq (xs w) (pvf1_rev_nodup adv w) (pvf1_rev_all adv w)
        (Rint M (A w) w') w'
      have hdiff : sumOn (xs w) (Rint M (A w) w') (fun i => w' (xs w)[i]) -
          sumOn (xs w) (Rint M (A w) w') (thrAt rule M (xs w) w) ≤ h (w, w') := by
        show _ ≤ sumOn (xs w) (Rint M (A w) w')
          (fun i => max (w' (xs w)[i] - thrAt rule M (xs w) w i) 0)
        unfold sumOn
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_le_sum fun i _ => ?_
        split_ifs
        · exact le_max_left _ _
        · simp
      unfold MatroidProphetKW.Single.wt at hwt ⊢
      change _ ≤ (1 / a) * kR (A w) at h14w
      linarith
    have hi1 : Integrable (fun w' => MatroidProphetKW.Single.wt w' (Rint M (A w) w') -
        (1 / a) * kR (A w)) (law F) :=
      (pvf1_int_wtD F hF_int _ (pvf1_Rint_ms M (A w))).sub (integrable_const _)
    have := integral_mono hi1 (hint_h w) hpt
    rw [integral_sub (pvf1_int_wtD F hF_int _ (pvf1_Rint_ms M (A w))) (integrable_const _)] at this
    simpa using this
  have hL : Integrable (fun w => kR' (A w) - (1 / a) * kR (A w)) (law F) :=
    (pvf1_int_ofA F rule M adv kR').sub ((pvf1_int_ofA F rule M adv kR).const_mul _)
  have := integral_mono_ae hL hH hptw
  rw [integral_sub (pvf1_int_ofA F rule M adv kR') ((pvf1_int_ofA F rule M adv kR).const_mul _),
    integral_const_mul] at this
  exact this

end Eq24

section Eq23A

open MatroidProphetKW.Inter

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- the prefix `[x_1, …, x_k]` revealed by the adversary -/
def pvf1L (adv : Adversary α) (w : α → ℝ) (k : ℕ) : List α :=
  (fun xs => xs ++ [adv.next xs w])^[k] []

/-- the element revealed at (0-based) step `k` -/
def pvf1x (adv : Adversary α) (w : α → ℝ) (k : ℕ) : α := adv.next (pvf1L adv w k) w

/-- the set selected before step `k` -/
noncomputable def pvf1A {p : ℕ} (rule : ThresholdRule α) (M : Fin p → Matroid α)
    (adv : Adversary α) (w : α → ℝ) (k : ℕ) : Finset α :=
  sel rule M (pvf1L adv w k) w k

/-- the threshold offered at step `k` -/
noncomputable def pvf1T {p : ℕ} (rule : ThresholdRule α) (M : Fin p → Matroid α)
    (adv : Adversary α) (w : α → ℝ) (k : ℕ) : ℝ :=
  rule.thr (pvf1A rule M adv w k) (pvf1L adv w k) w (pvf1x adv w k)

theorem pvf1_iter_append (adv : Adversary α) (w : α → ℝ) (m : ℕ) (l : List α) :
    ∃ r, (fun xs => xs ++ [adv.next xs w])^[m] l = l ++ r := by
  induction m generalizing l with
  | zero => exact ⟨[], by simp⟩
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    obtain ⟨r, hr⟩ := ih (l ++ [adv.next l w])
    exact ⟨[adv.next l w] ++ r, by rw [hr, List.append_assoc]⟩

theorem pvf1L_succ (adv : Adversary α) (w : α → ℝ) (k : ℕ) :
    pvf1L adv w (k + 1) = pvf1L adv w k ++ [pvf1x adv w k] := by
  unfold pvf1L pvf1x
  rw [Function.iterate_succ_apply']
  rfl

theorem pvf1L_len (adv : Adversary α) (w : α → ℝ) (k : ℕ) (hk : k ≤ Fintype.card α) :
    (pvf1L adv w k).length = k := (pvf1_iter_props adv w k hk).2

theorem pvf1_rev_split (adv : Adversary α) (w : α → ℝ) (k : ℕ) (hk : k ≤ Fintype.card α) :
    ∃ r, revealOrder adv w = pvf1L adv w k ++ r := by
  have : revealOrder adv w =
      (fun xs => xs ++ [adv.next xs w])^[Fintype.card α - k] (pvf1L adv w k) := by
    unfold revealOrder pvf1L
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hk]
  rw [this]
  exact pvf1_iter_append adv w _ _

theorem pvf1_rev_get (adv : Adversary α) (w : α → ℝ) (k : ℕ) (hk : k < Fintype.card α)
    (h : k < (revealOrder adv w).length) : (revealOrder adv w)[k] = pvf1x adv w k := by
  obtain ⟨r, hr⟩ := pvf1_rev_split adv w (k + 1) hk
  have hlen := pvf1L_len adv w k hk.le
  rw [List.getElem_of_eq hr h]
  simp [pvf1L_succ, hlen]

theorem pvf1_rev_take (adv : Adversary α) (w : α → ℝ) (k : ℕ) (hk : k ≤ Fintype.card α) :
    (revealOrder adv w).take k = pvf1L adv w k := by
  obtain ⟨r, hr⟩ := pvf1_rev_split adv w k hk
  rw [hr]
  exact List.take_left' (pvf1L_len adv w k hk)

theorem pvf1_sel_append {p : ℕ} (rule : ThresholdRule α) (M : Fin p → Matroid α)
    (l r : List α) (w : α → ℝ) (k : ℕ) (hk : k ≤ l.length) :
    sel rule M (l ++ r) w k = sel rule M l w k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk' : k < l.length := hk
    have h1 : k < (l ++ r).length := by simp; omega
    simp only [sel, dif_pos hk', dif_pos h1]
    rw [ih (by omega), List.getElem_append_left hk', List.take_append_of_le_length hk'.le]

theorem pvf1_rev_sel {p : ℕ} (rule : ThresholdRule α) (M : Fin p → Matroid α)
    (adv : Adversary α) (w : α → ℝ) (k : ℕ) (hk : k ≤ Fintype.card α) :
    sel rule M (revealOrder adv w) w k = pvf1A rule M adv w k := by
  obtain ⟨r, hr⟩ := pvf1_rev_split adv w k hk
  rw [hr, pvf1_sel_append rule M _ r w k (by rw [pvf1L_len adv w k hk])]
  rfl

theorem pvf1_sel_agree {p : ℕ} (rule : ThresholdRule α) (M : Fin p → Matroid α)
    (l : List α) (w w' : α → ℝ) (hag : ∀ y ∈ l, w' y = w y) (k : ℕ) :
    sel rule M l w' k = sel rule M l w k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    by_cases h : k < l.length
    · have h1 : rule.thr (sel rule M l w k) (l.take k) w' l[k] =
          rule.thr (sel rule M l w k) (l.take k) w l[k] :=
        rule.online _ _ _ _ _ (fun y hy => hag y (List.mem_of_mem_take hy))
      have hc : (IsIndep M (insert l[k] (sel rule M l w' k)) ∧
          rule.thr (sel rule M l w' k) (l.take k) w' l[k] ≤ w' l[k]) ↔
          (IsIndep M (insert l[k] (sel rule M l w k)) ∧
          rule.thr (sel rule M l w k) (l.take k) w l[k] ≤ w l[k]) := by
        rw [ih, h1, hag l[k] (List.getElem_mem h)]
      simp only [sel, dif_pos h]
      split_ifs with c1 c2 c2
      · rw [ih]
      · exact absurd (hc.1 c1) c2
      · exact absurd (hc.2 c2) c1
      · exact ih
    · simp only [sel, dif_neg h]
      exact ih

theorem pvf1L_agree (adv : Adversary α) (w w' : α → ℝ) (k : ℕ)
    (hag : ∀ y ∈ pvf1L adv w k, w' y = w y) : pvf1L adv w' k = pvf1L adv w k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pvf1L_succ] at hag
    have hag' : ∀ y ∈ pvf1L adv w k, w' y = w y := fun y hy => hag y (List.mem_append_left _ hy)
    rw [pvf1L_succ, pvf1L_succ, ih hag']
    unfold pvf1x
    rw [ih hag', adv.online _ w' w (fun y hy => hag' y hy)]

theorem pvf1_step_L (adv : Adversary α) (k : ℕ) (hk : k < Fintype.card α) (w : α → ℝ)
    (t : ℝ) : (∀ y ∈ pvf1L adv w k, Function.update w (pvf1x adv w k) t y = w y) ∧
      pvf1L adv (Function.update w (pvf1x adv w k) t) k = pvf1L adv w k ∧
      pvf1x adv (Function.update w (pvf1x adv w k) t) k = pvf1x adv w k := by
  have hnd : (pvf1L adv w k).Nodup := (pvf1_iter_props adv w k hk.le).1
  have hlen := pvf1L_len adv w k hk.le
  have hex : ∃ y, y ∉ pvf1L adv w k := by
    by_contra hcon
    push_neg at hcon
    have hsub : (Finset.univ : Finset α) ⊆ (pvf1L adv w k).toFinset :=
      fun y _ => List.mem_toFinset.2 (hcon y)
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_univ, List.toFinset_card_of_nodup hnd, hlen] at h1
    omega
  have hnot : pvf1x adv w k ∉ pvf1L adv w k := adv.fresh _ w hex
  have hag : ∀ y ∈ pvf1L adv w k, Function.update w (pvf1x adv w k) t y = w y :=
    fun y hy => Function.update_of_ne (fun h : y = pvf1x adv w k => hnot (h ▸ hy)) _ _
  have hL := pvf1L_agree adv w (Function.update w (pvf1x adv w k) t) k hag
  refine ⟨hag, hL, ?_⟩
  show adv.next (pvf1L adv (Function.update w (pvf1x adv w k) t) k)
    (Function.update w (pvf1x adv w k) t) = pvf1x adv w k
  rw [hL, adv.online _ _ w hag]
  rfl

/-- invariance of step `k` under changing the weight of the element revealed at step `k` -/
theorem pvf1_step_inv {p : ℕ} (rule : ThresholdRule α) (M : Fin p → Matroid α)
    (adv : Adversary α) (k : ℕ) (hk : k < Fintype.card α) (w : α → ℝ) (t : ℝ) :
    pvf1A rule M adv (Function.update w (pvf1x adv w k) t) k = pvf1A rule M adv w k ∧
    pvf1T rule M adv (Function.update w (pvf1x adv w k) t) k = pvf1T rule M adv w k := by
  obtain ⟨hag, hL, hX⟩ := pvf1_step_L adv k hk w t
  have hA : pvf1A rule M adv (Function.update w (pvf1x adv w k) t) k = pvf1A rule M adv w k := by
    unfold pvf1A
    rw [hL, pvf1_sel_agree rule M _ w _ hag]
  refine ⟨hA, ?_⟩
  unfold pvf1T
  rw [hA, hL, hX]
  exact rule.online _ _ _ _ _ (fun y hy => hag y hy)

theorem pvf1_step_x_iff (adv : Adversary α) (k : ℕ) (hk : k < Fintype.card α) (w : α → ℝ)
    (x : α) (t : ℝ) : pvf1x adv (Function.update w x t) k = x ↔ pvf1x adv w k = x := by
  constructor
  · intro h
    have := (pvf1_step_L adv k hk (Function.update w x t) (w x)).2.2
    rw [h, Function.update_idem, Function.update_eq_self] at this
    exact this
  · intro h
    have := (pvf1_step_L adv k hk w t).2.2
    rw [h] at this
    exact this

end Eq23A

section Eq23B

open MatroidProphetKW.Inter

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem pvf1x_ms (adv : Adversary α) (k : ℕ) (x : α) :
    MeasurableSet {w : α → ℝ | pvf1x adv w k = x} :=
  pvf1_dm_comp (fun w => pvf1L adv w k) (pvf1_iter_ms adv k) (fun l w => adv.next l w)
    (fun l y => adv.meas l y) x

theorem pvf1P_ms {p : ℕ} (rule : ThresholdRule α) (M : Fin p → Matroid α) (adv : Adversary α)
    (k : ℕ) (q : List α × Finset α × α) :
    MeasurableSet {w : α → ℝ | (pvf1L adv w k, pvf1A rule M adv w k, pvf1x adv w k) = q} := by
  have : {w : α → ℝ | (pvf1L adv w k, pvf1A rule M adv w k, pvf1x adv w k) = q} =
      {w | pvf1L adv w k = q.1} ∩ ({w | pvf1A rule M adv w k = q.2.1} ∩
        {w | pvf1x adv w k = q.2.2}) := by
    ext w; simp [Prod.ext_iff]
  rw [this]
  exact (pvf1_iter_ms adv k _).inter
    ((pvf1_dm_comp (fun w => pvf1L adv w k) (pvf1_iter_ms adv k) (fun l w => sel rule M l w k)
      (fun l S => pvf1_sel_ms rule M l k S) _).inter (pvf1x_ms adv k _))

theorem pvf1T_meas {p : ℕ} (rule : ThresholdRule α) (M : Fin p → Matroid α) (adv : Adversary α)
    (k : ℕ) : Measurable (fun w => pvf1T rule M adv w k) :=
  pvf1_meas_comp (fun w => (pvf1L adv w k, pvf1A rule M adv w k, pvf1x adv w k))
    (pvf1P_ms rule M adv k) (fun q w => rule.thr q.2.1 q.1 w q.2.2) (fun q => rule.meas _ _ _)

theorem pvf1feas_ms {p : ℕ} (rule : ThresholdRule α) (M : Fin p → Matroid α)
    (adv : Adversary α) (k : ℕ) :
    MeasurableSet {w : α → ℝ | IsIndep M (insert (pvf1x adv w k) (pvf1A rule M adv w k))} :=
  pvf1_ms_of_disc (fun w => (pvf1L adv w k, pvf1A rule M adv w k, pvf1x adv w k))
    (pvf1P_ms rule M adv k) {q | IsIndep M (insert q.2.2 q.2.1)}

/-- the surplus collected at step `k`, evaluated with weights `v` -/
noncomputable def pvf1Q {p : ℕ} (rule : ThresholdRule α) (M : Fin p → Matroid α)
    (adv : Adversary α) (k : ℕ) (w v : α → ℝ) : ℝ := by
  classical
  exact if IsIndep M (insert (pvf1x adv w k) (pvf1A rule M adv w k)) then
    max (v (pvf1x adv w k) - pvf1T rule M adv w k) 0 else 0

theorem pvf1Q_meas_gen {p : ℕ} (rule : ThresholdRule α) (M : Fin p → Matroid α)
    (adv : Adversary α) (k : ℕ) {β : Type*} [MeasurableSpace β] (f g : β → α → ℝ)
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun b => pvf1Q rule M adv k (f b) (g b)) := by
  classical
  unfold pvf1Q
  refine Measurable.ite (hf (pvf1feas_ms rule M adv k)) ?_ measurable_const
  refine (Measurable.sub ?_ ((pvf1T_meas rule M adv k).comp hf)).max measurable_const
  exact pvf1_meas_comp (fun b => pvf1x adv (f b) k)
    (fun y => hf (pvf1x_ms adv k y)) (fun y b => g b y)
    (fun y => (measurable_pi_apply y).comp hg)

theorem pvf1Q_bd {p : ℕ} (rule : ThresholdRule α) (M : Fin p → Matroid α)
    (adv : Adversary α) (hthr : ∀ A xs w x, 0 ≤ rule.thr A xs w x) (k : ℕ) (w v : α → ℝ) :
    0 ≤ pvf1Q rule M adv k w v ∧ pvf1Q rule M adv k w v ≤ ∑ y, |v y| := by
  have hT : 0 ≤ pvf1T rule M adv w k := hthr _ _ _ _
  have h1 : |v (pvf1x adv w k)| ≤ ∑ y, |v y| :=
    Finset.single_le_sum (f := fun y => |v y|) (fun y _ => abs_nonneg _) (Finset.mem_univ _)
  unfold pvf1Q
  split_ifs
  · exact ⟨le_max_right _ _, (max_le (by linarith [le_abs_self (v (pvf1x adv w k))])
      (abs_nonneg _)).trans h1⟩
  · exact ⟨le_rfl, Finset.sum_nonneg fun y _ => abs_nonneg _⟩

theorem pvf1_facts (rule : ThresholdRule α) {p : ℕ} (M : Fin p → Matroid α) (adv : Adversary α)
    (w : α → ℝ) (i : Fin (revealOrder adv w).length) :
    (i : ℕ) < Fintype.card α ∧ (revealOrder adv w)[i] = pvf1x adv w i ∧
      sel rule M (revealOrder adv w) w i = pvf1A rule M adv w i ∧
      thrAt rule M (revealOrder adv w) w i = pvf1T rule M adv w i := by
  have hi : (i : ℕ) < Fintype.card α := by rw [← pvf1_rev_len adv w]; exact i.2
  have hx := pvf1_rev_get adv w i hi i.2
  have hA := pvf1_rev_sel rule M adv w i hi.le
  refine ⟨hi, hx, hA, ?_⟩
  unfold thrAt pvf1T
  rw [hA, pvf1_rev_take adv w i hi.le]
  exact congrArg (rule.thr _ _ w) hx

/-- the collected surplus is the sum of the step surpluses -/
theorem pvf1_U_eq {p : ℕ} (rule : ThresholdRule α) (M : Fin p → Matroid α) (adv : Adversary α)
    (w : α → ℝ) :
    sumOn (revealOrder adv w) (adaptiveSelected rule M adv w)
        (fun i => max (w (revealOrder adv w)[i] - thrAt rule M (revealOrder adv w) w i) 0) =
      ∑ k ∈ Finset.range (Fintype.card α), pvf1Q rule M adv k w w := by
  classical
  have hs : ∀ i : Fin (revealOrder adv w).length,
      (if (revealOrder adv w)[i] ∈ adaptiveSelected rule M adv w then
        max (w (revealOrder adv w)[i] - thrAt rule M (revealOrder adv w) w i) 0 else 0) =
      pvf1Q rule M adv i w w := by
    intro i
    obtain ⟨hi, hx, hA, hT⟩ := pvf1_facts rule M adv w i
    have hmem := pvf1_mem_selected_iff rule M (revealOrder adv w) (pvf1_rev_nodup adv w) w i
    rw [hx, hA, hT] at hmem
    have hmem' : pvf1x adv w i ∈ adaptiveSelected rule M adv w ↔
        IsIndep M (insert (pvf1x adv w i) (pvf1A rule M adv w i)) ∧
          pvf1T rule M adv w i ≤ w (pvf1x adv w i) := hmem
    rw [hx, hT]
    unfold pvf1Q
    by_cases h1 : IsIndep M (insert (pvf1x adv w i) (pvf1A rule M adv w i))
    · by_cases h2 : pvf1T rule M adv w i ≤ w (pvf1x adv w i)
      · rw [if_pos (hmem'.2 ⟨h1, h2⟩), if_pos h1]
      · rw [if_neg (fun h => h2 (hmem'.1 h).2), if_pos h1, max_eq_right (by linarith)]
    · rw [if_neg (fun h => h1 (hmem'.1 h).1), if_neg h1]
  unfold sumOn
  calc _ = ∑ i : Fin (revealOrder adv w).length, pvf1Q rule M adv i w w :=
        Finset.sum_congr rfl (fun i _ => hs i)
    _ = ∑ k ∈ Finset.range (revealOrder adv w).length, pvf1Q rule M adv k w w :=
        Fin.sum_univ_eq_sum_range (fun k => pvf1Q rule M adv k w w) _
    _ = _ := by rw [pvf1_rev_len]

/-- the ghost surplus on `R(A)` is at most the sum of the ghost step surpluses -/
theorem pvf1_V_le {p : ℕ} (rule : ThresholdRule α) (M : Fin p → Matroid α) (adv : Adversary α)
    (w w' : α → ℝ) :
    sumOn (revealOrder adv w) (Rint M (adaptiveSelected rule M adv w) w')
        (fun i => max (w' (revealOrder adv w)[i] - thrAt rule M (revealOrder adv w) w i) 0) ≤
      ∑ k ∈ Finset.range (Fintype.card α), pvf1Q rule M adv k w w' := by
  classical
  have hAi : IsIndep M (adaptiveSelected rule M adv w) := pvf1_sel_indep rule M _ w _
  have hs : ∀ i : Fin (revealOrder adv w).length,
      (if (revealOrder adv w)[i] ∈ Rint M (adaptiveSelected rule M adv w) w' then
        max (w' (revealOrder adv w)[i] - thrAt rule M (revealOrder adv w) w i) 0 else 0) ≤
      pvf1Q rule M adv i w w' := by
    intro i
    obtain ⟨hi, hx, hA, hT⟩ := pvf1_facts rule M adv w i
    have hsub : sel rule M (revealOrder adv w) w i ⊆ adaptiveSelected rule M adv w :=
      pvf1_sel_mono rule M _ w i.2.le
    rw [hA] at hsub
    rw [hx, hT]
    unfold pvf1Q
    split_ifs with h1 h2
    · exact le_rfl
    · exfalso
      apply h2
      have hind := pvf1_Rint_indep M _ hAi w'
      intro j
      apply (hind j).subset
      have : insert (pvf1x adv w i) (pvf1A rule M adv w i) ⊆
          adaptiveSelected rule M adv w ∪ Rint M (adaptiveSelected rule M adv w) w' :=
        Finset.insert_subset (Finset.mem_union_right _ h1)
          (hsub.trans Finset.subset_union_left)
      exact_mod_cast this
    · exact le_max_right _ _
    · exact le_rfl
  unfold sumOn
  calc _ ≤ ∑ i : Fin (revealOrder adv w).length, pvf1Q rule M adv i w w' :=
        Finset.sum_le_sum (fun i _ => hs i)
    _ = ∑ k ∈ Finset.range (revealOrder adv w).length, pvf1Q rule M adv k w w' :=
        Fin.sum_univ_eq_sum_range (fun k => pvf1Q rule M adv k w w') _
    _ = _ := by rw [pvf1_rev_len]

theorem pvf1_mp_update (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)] (x : α) :
    MeasurePreserving (fun q : (α → ℝ) × ℝ => Function.update q.1 x q.2)
      ((law F).prod (F x)) (law F) := by
  haveI : IsProbabilityMeasure (law F) := by unfold law; infer_instance
  refine ⟨measurable_update', Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply measurable_update' hs, Measure.prod_apply (measurable_update' hs)]
  have h := pvf1_lint_update F x (s.indicator 1) (measurable_one.indicator hs)
  rw [lintegral_indicator_one hs] at h
  rw [h]
  congr 1
  funext w
  rw [← lintegral_indicator_one (measurable_prodMk_left (measurable_update' (a := x) hs))]
  congr 1

theorem pvf1_int_update (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)] (x : α)
    (f : (α → ℝ) → ℝ) (hf : Integrable f (law F)) :
    Integrable (fun w => ∫ t, f (Function.update w x t) ∂(F x)) (law F) ∧
    ∫ w, f w ∂(law F) = ∫ w, ∫ t, f (Function.update w x t) ∂(F x) ∂(law F) := by
  haveI : IsProbabilityMeasure (law F) := by unfold law; infer_instance
  have mp := pvf1_mp_update F x
  have hint : Integrable (f ∘ fun q : (α → ℝ) × ℝ => Function.update q.1 x q.2)
      ((law F).prod (F x)) := mp.integrable_comp_of_integrable hf
  refine ⟨hint.integral_prod_left, ?_⟩
  conv_lhs => rw [← mp.map_eq]
  rw [integral_map mp.measurable.aemeasurable (by rw [mp.map_eq]; exact hf.aestronglyMeasurable)]
  exact integral_prod _ hint

theorem pvf1_int_eval (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)] (x : α) (c : ℝ) :
    ∫ w', max (w' x - c) 0 ∂(law F) = ∫ t, max (t - c) 0 ∂(F x) := by
  have := integral_map (μ := law F) (φ := fun w' : α → ℝ => w' x)
    (measurable_pi_apply x).aemeasurable (f := fun t => max (t - c) 0)
    ((measurable_id.sub_const c).max measurable_const).aestronglyMeasurable
  rw [show (law F).map (fun w' : α → ℝ => w' x) = F x from (measurePreserving_eval F x).map_eq]
    at this
  exact this.symm

end Eq23B

section Eq23C

open MatroidProphetKW.Inter

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem pvf1Q_diag_int {p : ℕ} (rule : ThresholdRule α) (M : Fin p → Matroid α)
    (adv : Adversary α) (hthr : ∀ A xs w x, 0 ≤ rule.thr A xs w x)
    (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)] (hF_int : ∀ x, Integrable id (F x))
    (k : ℕ) : Integrable (fun w => pvf1Q rule M adv k w w) (law F) := by
  have hm : Measurable (fun w => pvf1Q rule M adv k w w) :=
    pvf1Q_meas_gen rule M adv k id id measurable_id measurable_id
  refine (pvf1_int_absSum F hF_int).mono' hm.aestronglyMeasurable (ae_of_all _ fun w => ?_)
  obtain ⟨h0, h1⟩ := pvf1Q_bd rule M adv hthr k w w
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact h1

theorem pvf1Q_slice_int {p : ℕ} (rule : ThresholdRule α) (M : Fin p → Matroid α)
    (adv : Adversary α) (hthr : ∀ A xs w x, 0 ≤ rule.thr A xs w x)
    (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)] (hF_int : ∀ x, Integrable id (F x))
    (k : ℕ) (w : α → ℝ) : Integrable (fun w' => pvf1Q rule M adv k w w') (law F) := by
  have hm : Measurable (fun w' => pvf1Q rule M adv k w w') :=
    pvf1Q_meas_gen rule M adv k (fun _ => w) id measurable_const measurable_id
  refine (pvf1_int_absSum F hF_int).mono' hm.aestronglyMeasurable (ae_of_all _ fun w' => ?_)
  obtain ⟨h0, h1⟩ := pvf1Q_bd rule M adv hthr k w w'
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact h1

/-- the key probabilistic step: at step `k`, the ghost surplus and the real surplus have the
same expectation, because the step data do not depend on the weight of `x_k`. -/
theorem pvf1_step_eq {p : ℕ} (rule : ThresholdRule α) (M : Fin p → Matroid α)
    (adv : Adversary α) (hthr : ∀ A xs w x, 0 ≤ rule.thr A xs w x)
    (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)] (hF_int : ∀ x, Integrable id (F x))
    (k : ℕ) (hk : k < Fintype.card α) :
    Integrable (fun w => ∫ w', pvf1Q rule M adv k w w' ∂(law F)) (law F) ∧
    ∫ w, ∫ w', pvf1Q rule M adv k w w' ∂(law F) ∂(law F) =
      ∫ w, pvf1Q rule M adv k w w ∂(law F) := by
  classical
  haveI : IsProbabilityMeasure (law F) := by unfold law; infer_instance
  -- the step-`k` data
  set X : (α → ℝ) → α := fun w => pvf1x adv w k with hXdef
  set T : (α → ℝ) → ℝ := fun w => pvf1T rule M adv w k with hTdef
  set fe : (α → ℝ) → Prop :=
    fun w => IsIndep M (insert (pvf1x adv w k) (pvf1A rule M adv w k)) with hfedef
  let Φ : α → ℝ → ℝ := fun x c => ∫ t, max (t - c) 0 ∂(F x)
  let hx : α → (α → ℝ) → ℝ := fun x w => if X w = x then (if fe w then Φ x (T w) else 0) else 0
  have hin : ∀ w, ∫ w', pvf1Q rule M adv k w w' ∂(law F) = ∑ x, hx x w := by
    intro w
    have e1 : ∫ w', pvf1Q rule M adv k w w' ∂(law F) = if fe w then Φ (X w) (T w) else 0 := by
      unfold pvf1Q
      by_cases h : fe w
      · simp only [hfedef] at h
        rw [if_pos h]
        simp only [if_pos h]
        exact pvf1_int_eval F _ _
      · simp only [hfedef] at h
        rw [if_neg h]
        simp only [if_neg h, integral_zero]
    rw [e1]
    simp only [hx]
    rw [Finset.sum_ite_eq]
    simp
  let g : α → (α → ℝ) → ℝ := fun x w => if X w = x then pvf1Q rule M adv k w w else 0
  have hdiag : ∀ w, pvf1Q rule M adv k w w = ∑ x, g x w := by
    intro w
    simp only [g]
    rw [Finset.sum_ite_eq]
    simp
  have hgi : ∀ x, Integrable (g x) (law F) := by
    intro x
    have hm : Measurable (g x) :=
      Measurable.ite (pvf1x_ms adv k x)
        (pvf1Q_meas_gen rule M adv k id id measurable_id measurable_id) measurable_const
    refine (pvf1_int_absSum F hF_int).mono' hm.aestronglyMeasurable (ae_of_all _ fun w => ?_)
    obtain ⟨h0, h1⟩ := pvf1Q_bd rule M adv hthr k w w
    rw [Real.norm_eq_abs]
    simp only [g]
    split_ifs
    · rw [abs_of_nonneg h0]; exact h1
    · simp only [abs_zero]; exact Finset.sum_nonneg fun y _ => abs_nonneg _
  have hgu : ∀ x w t, g x (Function.update w x t) =
      if X w = x then (if fe w then max (t - T w) 0 else 0) else 0 := by
    intro x w t
    by_cases hxw : X w = x
    · have hxw' : pvf1x adv w k = x := hxw
      subst hxw'
      obtain ⟨-, -, hX⟩ := pvf1_step_L adv k hk w t
      obtain ⟨hA, hT⟩ := pvf1_step_inv rule M adv k hk w t
      simp only [g, hXdef, hTdef, hfedef, hX, if_true]
      unfold pvf1Q
      rw [hX, hA, hT, Function.update_self]
    · have hn : ¬ X (Function.update w x t) = x :=
        fun h => hxw ((pvf1_step_x_iff adv k hk w x t).1 h)
      simp only [g, if_neg hn, if_neg hxw]
  have hgt : ∀ x w, ∫ t, g x (Function.update w x t) ∂(F x) = hx x w := by
    intro x w
    simp only [hgu x w, hx]
    by_cases h1 : X w = x
    · by_cases h2 : fe w
      · simp only [if_pos h1, if_pos h2]
        rfl
      · simp only [if_pos h1, if_neg h2, integral_zero]
    · simp only [if_neg h1, integral_zero]
  have hxi : ∀ x, Integrable (hx x) (law F) := by
    intro x
    have := (pvf1_int_update F x (g x) (hgi x)).1
    simp only [hgt x] at this
    exact this
  have hxe : ∀ x, ∫ w, hx x w ∂(law F) = ∫ w, g x w ∂(law F) := by
    intro x
    rw [(pvf1_int_update F x (g x) (hgi x)).2]
    simp only [hgt x]
  refine ⟨?_, ?_⟩
  · simp only [hin]
    exact integrable_finsetSum _ (fun x _ => hxi x)
  · simp only [hin, hdiag]
    rw [integral_finsetSum _ (fun x _ => hxi x), integral_finsetSum _ (fun x _ => hgi x)]
    exact Finset.sum_congr rfl (fun x _ => hxe x)

theorem pvf1_eq23 {p : ℕ} (M : Fin p → Matroid α)
    (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)] (hF_int : ∀ x, Integrable id (F x))
    (rule : ThresholdRule α) (hthr : ∀ A xs w x, 0 ≤ rule.thr A xs w x)
    (adv : Adversary α) :
    ∫ w, ∫ w', sumOn (revealOrder adv w) (Rint M (adaptiveSelected rule M adv w) w')
        (fun i => max (w' (revealOrder adv w)[i] - thrAt rule M (revealOrder adv w) w i) 0)
        ∂(law F) ∂(law F) ≤
      ∫ w, sumOn (revealOrder adv w) (adaptiveSelected rule M adv w)
        (fun i => max (w (revealOrder adv w)[i] - thrAt rule M (revealOrder adv w) w i) 0)
        ∂(law F) := by
  haveI : IsProbabilityMeasure (law F) := by unfold law; infer_instance
  set n := Fintype.card α
  let h : (α → ℝ) × (α → ℝ) → ℝ := fun ω =>
    sumOn (revealOrder adv ω.1) (Rint M (adaptiveSelected rule M adv ω.1) ω.2)
      (fun i => max (ω.2 (revealOrder adv ω.1)[i] -
        thrAt rule M (revealOrder adv ω.1) ω.1 i) 0)
  have hm : Measurable h := pvf1_h_meas rule M adv
  have hbd : ∀ ω, h ω ≤ ∑ x, |ω.2 x| := fun ω =>
    pvf1_sumOn_le_abs (revealOrder adv ω.1) (pvf1_rev_nodup adv _) (pvf1_rev_all adv _) _ _ _
      (fun i => hthr _ _ _ _)
  have hnn_h : ∀ ω, 0 ≤ h ω := fun ω => pvf1_sumOn_nonneg _ _ _ (fun i => le_max_right _ _)
  have hint_h : ∀ w, Integrable (fun w' => h (w, w')) (law F) := by
    intro w
    refine (pvf1_int_absSum F hF_int).mono' (hm.comp measurable_prodMk_left).aestronglyMeasurable
      (ae_of_all _ fun w' => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn_h _)]
    exact hbd (w, w')
  have hH : Integrable (fun w => ∫ w', h (w, w') ∂(law F)) (law F) := by
    refine Integrable.of_bound
      (hm.stronglyMeasurable.integral_prod_right' (ν := law F)).aestronglyMeasurable
      (∫ w', ∑ x, |w' x| ∂(law F)) (ae_of_all _ fun w => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun w' => hnn_h _)]
    exact integral_mono (hint_h w) (pvf1_int_absSum F hF_int) (fun w' => hbd (w, w'))
  have hstep := fun k (hk : k ∈ Finset.range n) =>
    pvf1_step_eq rule M adv hthr F hF_int k (Finset.mem_range.1 hk)
  have hQi := pvf1Q_slice_int rule M adv hthr F hF_int
  have hmid : Integrable (fun w => ∫ w', ∑ k ∈ Finset.range n, pvf1Q rule M adv k w w' ∂(law F))
      (law F) := by
    have e : (fun w => ∫ w', ∑ k ∈ Finset.range n, pvf1Q rule M adv k w w' ∂(law F)) =
        fun w => ∑ k ∈ Finset.range n, ∫ w', pvf1Q rule M adv k w w' ∂(law F) :=
      funext fun w => integral_finsetSum _ (fun k _ => hQi k w)
    rw [e]
    exact integrable_finsetSum _ (fun k hk => (hstep k hk).1)
  calc ∫ w, ∫ w', h (w, w') ∂(law F) ∂(law F)
      ≤ ∫ w, ∫ w', ∑ k ∈ Finset.range n, pvf1Q rule M adv k w w' ∂(law F) ∂(law F) :=
        integral_mono hH hmid (fun w => integral_mono (hint_h w)
          (integrable_finsetSum _ (fun k _ => hQi k w)) (fun w' => pvf1_V_le rule M adv w w'))
    _ = ∫ w, ∑ k ∈ Finset.range n, ∫ w', pvf1Q rule M adv k w w' ∂(law F) ∂(law F) :=
        integral_congr_ae (ae_of_all _ fun w => integral_finsetSum _ (fun k _ => hQi k w))
    _ = ∑ k ∈ Finset.range n, ∫ w, ∫ w', pvf1Q rule M adv k w w' ∂(law F) ∂(law F) :=
        integral_finsetSum _ (fun k hk => (hstep k hk).1)
    _ = ∑ k ∈ Finset.range n, ∫ w, pvf1Q rule M adv k w w ∂(law F) :=
        Finset.sum_congr rfl (fun k hk => (hstep k hk).2)
    _ = ∫ w, ∑ k ∈ Finset.range n, pvf1Q rule M adv k w w ∂(law F) :=
        (integral_finsetSum _ (fun k _ => pvf1Q_diag_int rule M adv hthr F hF_int k)).symm
    _ = _ := integral_congr_ae (ae_of_all _ fun w => (pvf1_U_eq rule M adv w).symm)

end Eq23C

open MeasureTheory MatroidProphetKW.Inter in
theorem solution
    {α : Type*} [Fintype α] [DecidableEq α] {p : ℕ}
    (hp : 0 < p) (M : Fin p → Matroid α) (hE : ∀ j, (M j).E = Set.univ)
    (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)]
    (hF_nonneg : ∀ x, F x (Set.Iio 0) = 0) (hF_int : ∀ x, Integrable id (F x))
    (a : ℝ) (ha : 2 ≤ a) (rule : ThresholdRule α) (hthr : ∀ A xs w x, 0 ≤ rule.thr A xs w x)
    (hbal : IsBalanced M F a rule) (adv : Adversary α) :
    (a - p) / (a * (a - 1)) * ∫ w, OPT M w ∂(law F) ≤
      ∫ w, MatroidProphetKW.Single.wt w (adaptiveSelected rule M adv w) ∂(law F) := by
  exact pvf1_assembly hp M F hF_nonneg hF_int a ha rule hthr hbal.1 adv
    (pvf1_eq23 M F hF_int rule hthr adv)
    (pvf1_eq24 hp M F hF_nonneg hF_int a rule hthr hbal.2 adv)

