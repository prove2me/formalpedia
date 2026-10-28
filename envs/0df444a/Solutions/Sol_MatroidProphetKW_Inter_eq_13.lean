-- Prove2me | solution 1 for MatroidProphetKW.Inter.eq_13
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T19:44:21.637569+00:00
-- url     : https://prove2.me/submissions/8fe828b1-bfbe-4548-a9d4-97371af3c589

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

/-! ## Equation (13): telescoping -/

/-- `R_j(∅) = B`: the only admissible `R ⊆ B` with `R` independent and `B ⊆ cl_j(R)` is `B`. -/
theorem pv25_Rj_empty {p : ℕ} (M : Fin p → Matroid α) (j : Fin p) (w' : α → ℝ) :
    Rj M j ∅ w' = B M w' := by
  have hB : (M j).Indep (↑(B M w') : Set α) := (pvf1_B_spec M w').1 j
  have hcand : ∃ R, R ⊆ B M w' \ ∅ ∧ (M j).Indep (↑(∅ ∪ R) : Set α) ∧
      (↑(B M w') : Set α) ⊆ (M j).closure (↑(∅ ∪ R) : Set α) :=
    ⟨B M w', by simp, by simpa using hB, by simpa using (M j).subset_closure _ hB.subset_ground⟩
  have h : Rj M j ∅ w' ⊆ B M w' \ ∅ ∧ (M j).Indep (↑(∅ ∪ Rj M j ∅ w') : Set α) ∧
      (↑(B M w') : Set α) ⊆ (M j).closure (↑(∅ ∪ Rj M j ∅ w') : Set α) :=
    (pvf1_argmaxOn_spec _ (MatroidProphetKW.Single.wt w') hcand).1
  obtain ⟨hsub, hind, hcl⟩ := h
  rw [Finset.sdiff_empty] at hsub
  rw [Finset.empty_union] at hind hcl
  apply Finset.Subset.antisymm hsub
  intro b hb
  by_contra hbR
  have hbcl : b ∈ (M j).closure (↑(Rj M j ∅ w') : Set α) := hcl (Finset.mem_coe.2 hb)
  have hins : (M j).Indep (insert b (↑(Rj M j ∅ w') : Set α)) := by
    apply hB.subset
    intro y hy
    rcases hy with rfl | hy
    · exact Finset.mem_coe.2 hb
    · exact Finset.mem_coe.2 (hsub (Finset.mem_coe.1 hy))
  exact ((hind.insert_indep_iff_of_notMem (fun h => hbR (Finset.mem_coe.1 h))).1 hins).2 hbcl

/-- `G(A) = ∑_j (1/a) E[w′(R_j(A))]`. -/
noncomputable def pv25G {p : ℕ} (M : Fin p → Matroid α) (F : α → Measure ℝ)
    [∀ x, IsProbabilityMeasure (F x)] (a : ℝ) (A : Finset α) : ℝ :=
  ∑ j, (1 / a) * ∫ w', MatroidProphetKW.Single.wt w' (Rj M j A w') ∂(law F)

theorem pv25_Tsum_eq {p : ℕ} (M : Fin p → Matroid α) (F : α → Measure ℝ)
    [∀ x, IsProbabilityMeasure (F x)] (hF_int : ∀ x, Integrable id (F x)) (a : ℝ)
    (A : Finset α) (x : α) :
    Tsum M F a A x = pv25G M F a A - pv25G M F a (insert x A) := by
  unfold Tsum Tij pv25G
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_sub (pvf1_int_wtD F hF_int _ (pvf1_Rj_ms M j A))
    (pvf1_int_wtD F hF_int _ (pvf1_Rj_ms M j (insert x A)))]
  ring

theorem pv25_Gdiff {p : ℕ} (M : Fin p → Matroid α) (F : α → Measure ℝ)
    [∀ x, IsProbabilityMeasure (F x)] (hF_int : ∀ x, Integrable id (F x)) (a : ℝ)
    (A : Finset α) :
    pv25G M F a ∅ - pv25G M F a A =
      (1 / a) * ∫ w', ∑ j, MatroidProphetKW.Single.wt w' (Cj M j A w') ∂(law F) := by
  unfold pv25G
  rw [← Finset.sum_sub_distrib,
    integral_finsetSum _ (fun j _ => pvf1_int_wtD F hF_int _ (pvf1_Cj_ms M j A)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_sub, ← integral_sub (pvf1_int_wtD F hF_int _ (pvf1_Rj_ms M j ∅))
    (pvf1_int_wtD F hF_int _ (pvf1_Rj_ms M j A))]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards with w'
  rw [pv25_Rj_empty]
  unfold Cj MatroidProphetKW.Single.wt
  rw [← Finset.sum_sdiff (pvf1_Rj_sub_B M j A w')]
  ring

theorem pv25_sumOn_insert (xs : List α) (hnd : xs.Nodup) (S : Finset α)
    (g : Fin xs.length → ℝ) (k : ℕ) (hk : k < xs.length)
    (hS : ∀ i : Fin xs.length, xs[i] ∈ S → (i : ℕ) < k) :
    sumOn xs (insert xs[k] S) g = sumOn xs S g + g ⟨k, hk⟩ := by
  unfold sumOn
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨k, hk⟩ : Fin xs.length)),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨k, hk⟩ : Fin xs.length))]
  have hkS : xs[k] ∉ S := fun h => lt_irrefl k (hS ⟨k, hk⟩ h)
  have e1 : ∀ c : Decidable (xs[(⟨k, hk⟩ : Fin xs.length)] ∈ insert xs[k] S),
      @ite _ _ c (g ⟨k, hk⟩) 0 = g ⟨k, hk⟩ := fun c => if_pos (Finset.mem_insert_self _ _)
  have e2 : ∀ c : Decidable (xs[(⟨k, hk⟩ : Fin xs.length)] ∈ S),
      @ite _ _ c (g ⟨k, hk⟩) 0 = 0 := fun c => if_neg hkS
  rw [e1, e2]
  have e3 : ∑ i ∈ Finset.univ.erase (⟨k, hk⟩ : Fin xs.length),
      (if xs[i] ∈ insert xs[k] S then g i else 0) =
      ∑ i ∈ Finset.univ.erase (⟨k, hk⟩ : Fin xs.length), (if xs[i] ∈ S then g i else 0) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hik : i ≠ ⟨k, hk⟩ := Finset.ne_of_mem_erase hi
    have hne : xs[i] ≠ xs[k] := fun h => hik (Fin.ext ((hnd.getElem_inj_iff).1 h))
    by_cases h : xs[i] ∈ S
    · rw [if_pos (Finset.mem_insert_of_mem h), if_pos h]
    · have h' : xs[i] ∉ insert xs[k] S := by
        rw [Finset.mem_insert]; exact fun h2 => h2.elim hne h
      rw [if_neg h', if_neg h]
  rw [e3]
  ring

theorem pv25_partial {p : ℕ} (M : Fin p → Matroid α) (F : α → Measure ℝ)
    [∀ x, IsProbabilityMeasure (F x)] (hF_int : ∀ x, Integrable id (F x)) (a : ℝ)
    (xs : List α) (hnd : xs.Nodup) (w : α → ℝ) (k : ℕ) :
    sumOn xs (sel (sumRule M F a) M xs w k) (thrAt (sumRule M F a) M xs w) =
      pv25G M F a ∅ - pv25G M F a (sel (sumRule M F a) M xs w k) := by
  induction k with
  | zero =>
    simp only [sel, sub_self]
    unfold sumOn
    simp
  | succ k ih =>
    by_cases hk : k < xs.length
    · by_cases hc : IsIndep M (insert xs[k] (sel (sumRule M F a) M xs w k)) ∧
          (sumRule M F a).thr (sel (sumRule M F a) M xs w k) (xs.take k) w xs[k] ≤ w xs[k]
      · have hs : sel (sumRule M F a) M xs w (k + 1) =
            insert xs[k] (sel (sumRule M F a) M xs w k) := by
          simp only [sel, dif_pos hk, if_pos hc]
        have hS : ∀ i : Fin xs.length, xs[i] ∈ sel (sumRule M F a) M xs w k → (i : ℕ) < k := by
          intro i hi
          obtain ⟨i', h', hik, heq, -⟩ := pvf1_mem_sel (sumRule M F a) M xs w k _ hi
          have : i' = (i : ℕ) := (hnd.getElem_inj_iff).1 heq
          omega
        rw [hs, pv25_sumOn_insert xs hnd _ _ k hk hS, ih]
        have ht : thrAt (sumRule M F a) M xs w ⟨k, hk⟩ =
            Tsum M F a (sel (sumRule M F a) M xs w k) xs[k] := rfl
        rw [ht, pv25_Tsum_eq M F hF_int]
        ring
      · have hs : sel (sumRule M F a) M xs w (k + 1) = sel (sumRule M F a) M xs w k := by
          simp only [sel, dif_pos hk, if_neg hc]
        rw [hs, ih]
    · have hs : sel (sumRule M F a) M xs w (k + 1) = sel (sumRule M F a) M xs w k := by
        simp only [sel, dif_neg hk]
      rw [hs, ih]

end Infra

open MeasureTheory MatroidProphetKW.Inter in
theorem solution
    {α : Type*} [Fintype α] [DecidableEq α] {p : ℕ}
    (M : Fin p → Matroid α) (hE : ∀ j, (M j).E = Set.univ)
    (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)]
    (hF_nonneg : ∀ x, F x (Set.Iio 0) = 0) (hF_int : ∀ x, Integrable id (F x))
    (a : ℝ) (xs : List α) (hnd : xs.Nodup) (hall : ∀ x, x ∈ xs) (w : α → ℝ) :
    sumOn xs (selected (sumRule M F a) M xs w) (thrAt (sumRule M F a) M xs w) =
      (1 / a) * ∫ w', ∑ j, MatroidProphetKW.Single.wt w' (Cj M j (selected (sumRule M F a) M xs w) w') ∂(law F) := by
  unfold selected
  rw [pv25_partial M F hF_int a xs hnd w, pv25_Gdiff M F hF_int a]
