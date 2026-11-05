-- Prove2me | solution 1 for MultiPriceOnline.Ranking.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T07:49:08.790803+00:00
-- url     : https://prove2.me/submissions/12e0c4b8-db12-4c25-8bbd-e008ef58a377

import Mathlib
import Definitions.Def_MultiPriceOnline_Ranking_LP
import Definitions.Def_MultiPriceOnline_Ranking_Setting
import Theorems.Thm_MultiPriceOnline_Ranking_lemma_2
import Theorems.Thm_MultiPriceOnline_Ranking_lemma_3
import Theorems.Thm_MultiPriceOnline_Ranking_weak_duality

open MeasureTheory MultiPriceOnline.Ranking Finset

namespace MPR2Aux

/-! ### Elementary facts about price sets and `Φ` -/

lemma pr_diff_pos {m : ℕ} {r : ℕ → ℝ} (hr : MultiPriceOnline.Ranking.IsPriceSet m r) :
    ∀ j, 1 ≤ j → j ≤ m → 0 < r j - MultiPriceOnline.Balance.pr r (j - 1) := by
  intro j hj1 hjm
  rcases eq_or_lt_of_le hj1 with h | h
  · rw [← h]
    change 0 < r 1 - MultiPriceOnline.Balance.pr r 0
    unfold MultiPriceOnline.Balance.pr
    simp [hr.2.1]
  · have hrj1 : MultiPriceOnline.Balance.pr r (j - 1) = r (j - 1) := if_neg (by omega)
    rw [hrj1]
    have hlt := hr.2.2 (j - 1) (by omega) (by omega)
    have heq : j - 1 + 1 = j := by omega
    rw [heq] at hlt
    linarith

lemma ell_bounds (m : ℕ) (hm : 1 ≤ m) (α : ℕ → ℝ) (w : ℝ) :
    1 ≤ ell m α w ∧ ell m α w ≤ m := by
  unfold ell
  have hsub : ((Icc 1 (m - 1)).filter (fun j => L α j ≤ w)).card ≤ (Icc 1 (m - 1)).card :=
    card_filter_le _ _
  rw [Nat.card_Icc] at hsub
  omega

/-- The branch of `Φ` on segment `k`. -/
noncomputable def G (r α : ℕ → ℝ) (k : ℕ) (w : ℝ) : ℝ :=
  MultiPriceOnline.Balance.pr r (k - 1) +
    (r k - MultiPriceOnline.Balance.pr r (k - 1)) *
      (Real.exp (w - L α (k - 1)) - 1) / (Real.exp (α k) - 1)

lemma Phi_eq_G (m : ℕ) (r α : ℕ → ℝ) (w : ℝ) : Phi m r α w = G r α (ell m α w) w := rfl

lemma ell_mono (m : ℕ) (α : ℕ → ℝ) : Monotone (ell m α) := by
  intro w w' hww'
  unfold ell
  apply Nat.add_le_add_left
  apply card_le_card
  intro j hj
  simp only [mem_filter] at hj ⊢
  exact ⟨hj.1, le_trans hj.2 hww'⟩

lemma ell_meas (m : ℕ) (α : ℕ → ℝ) : Measurable (ell m α) := (ell_mono m α).measurable

lemma Phi_meas (m : ℕ) (r α : ℕ → ℝ) : Measurable (Phi m r α) := by
  have h : Measurable (fun q : ℝ × ℕ => G r α q.2 q.1) := by
    apply measurable_from_prod_countable_left
    intro k
    unfold G
    fun_prop
  exact h.comp (measurable_id.prodMk (ell_meas m α))

lemma PhiDeriv_nonneg {m : ℕ} {r α : ℕ → ℝ} (hr : MultiPriceOnline.Ranking.IsPriceSet m r)
    (hα : MultiPriceOnline.Balance.IsBookingLimits m r α) (w : ℝ) : 0 ≤ PhiDeriv m r α w := by
  unfold PhiDeriv
  have hb := ell_bounds m hr.1 α w
  have h1 := pr_diff_pos hr _ hb.1 hb.2
  have h2 : 0 < Real.exp (α (ell m α w)) - 1 := by
    rw [sub_pos, Real.one_lt_exp_iff]; exact hα.1 _ hb.1 hb.2
  positivity

/-- Level sets of `Φ` are Lebesgue-null. -/
lemma Phi_level_null {m : ℕ} {r α : ℕ → ℝ} (hr : MultiPriceOnline.Ranking.IsPriceSet m r)
    (hα : MultiPriceOnline.Balance.IsBookingLimits m r α) (c : ℝ) :
    (volume : Measure ℝ) {w | Phi m r α w = c} = 0 := by
  have hsub : {w | Phi m r α w = c} ⊆ ⋃ k : ℕ, {w | 1 ≤ k ∧ k ≤ m ∧ G r α k w = c} := by
    intro w hw
    simp only [Set.mem_ofPred_eq] at hw
    have hb := ell_bounds m hr.1 α w
    exact Set.mem_iUnion.2 ⟨ell m α w, hb.1, hb.2, hw⟩
  refine measure_mono_null hsub (measure_iUnion_null_iff.2 fun k => ?_)
  apply Set.Subsingleton.measure_zero
  rintro w1 ⟨hk1, hkm, h1⟩ w2 ⟨-, -, h2⟩
  have hb := pr_diff_pos hr k hk1 hkm
  have hd : 0 < Real.exp (α k) - 1 := by
    rw [sub_pos, Real.one_lt_exp_iff]; exact hα.1 _ hk1 hkm
  unfold G at h1 h2
  have he : Real.exp (w1 - L α (k - 1)) = Real.exp (w2 - L α (k - 1)) := by
    have h3 : (r k - MultiPriceOnline.Balance.pr r (k - 1)) *
        (Real.exp (w1 - L α (k - 1)) - 1) / (Real.exp (α k) - 1) =
        (r k - MultiPriceOnline.Balance.pr r (k - 1)) *
        (Real.exp (w2 - L α (k - 1)) - 1) / (Real.exp (α k) - 1) := by linarith
    rw [div_left_inj' hd.ne', mul_right_inj' hb.ne'] at h3
    linarith
  have := Real.exp_injective he
  linarith

/-! ### A two-coordinate null-set lemma for product measures -/

lemma null_pair {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, SigmaFinite (μ i)] {i i' : Fin n}
    (h : i ≠ i') {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hslice : ∀ c, μ i {x | f x = c} = 0) :
    Measure.pi μ {W | f (W i) = g (W i')} = 0 := by
  cases n with
  | zero => exact i.elim0
  | succ k =>
    obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq (x := i') (y := i) (Ne.symm h)
    have hmp := measurePreserving_piFinSuccAbove μ i
    set S : Set (ℝ × (Fin k → ℝ)) := {q | f q.1 = g (q.2 j)} with hSdef
    have hS : MeasurableSet S :=
      measurableSet_eq_fun (hf.comp measurable_fst)
        (hg.comp ((measurable_pi_apply j).comp measurable_snd))
    have hpre : {W : Fin (k + 1) → ℝ | f (W i) = g (W i')} =
        (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i) ⁻¹' S := by
      ext W
      simp [S, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv, Fin.removeNth, hj]
    rw [hpre, hmp.measure_preimage hS.nullMeasurableSet, Measure.prod_apply_symm hS]
    simp [S, hslice]

/-! ### Measurability -/

variable {n T : ℕ}

lemma score_meas (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ) (q : Fin n → ℕ → ℝ) (i : Fin n) :
    Measurable (fun W : Fin n → ℝ => score m r α q W i) := by
  unfold score
  exact measurable_const.sub ((Phi_meas _ _ _).comp (measurable_pi_apply i))

lemma scorevec_meas (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ) (q : Fin n → ℕ → ℝ) :
    Measurable (fun W : Fin n → ℝ => score m r α q W) :=
  measurable_pi_lambda _ fun i => score_meas m r α q i

/-- An explicit argmax rule: the smallest maximizer. -/
noncomputable def amax (C : Finset (Fin n)) (hC : C.Nonempty) (s : Fin n → ℝ) : Fin n :=
  (C.filter (fun i => ∀ j ∈ C, s j ≤ s i)).min' (by
    obtain ⟨i, hi, hmax⟩ := C.exists_max_image s hC
    exact ⟨i, mem_filter.2 ⟨hi, hmax⟩⟩)

lemma amax_spec (C : Finset (Fin n)) (hC : C.Nonempty) (s : Fin n → ℝ) :
    amax C hC s ∈ C ∧ ∀ j ∈ C, s j ≤ s (amax C hC s) := by
  have := min'_mem (C.filter (fun i => ∀ j ∈ C, s j ≤ s i)) (by
    obtain ⟨i, hi, hmax⟩ := C.exists_max_image s hC
    exact ⟨i, mem_filter.2 ⟨hi, hmax⟩⟩)
  exact mem_filter.1 this

lemma amax_meas (C : Finset (Fin n)) (hC : C.Nonempty) :
    Measurable (fun s : Fin n → ℝ => amax C hC s) := by
  apply measurable_to_countable'
  intro i
  have hset : (fun s : Fin n → ℝ => amax C hC s) ⁻¹' {i} =
      {s | (i ∈ C ∧ ∀ j ∈ C, s j ≤ s i) ∧
        ∀ b, (b ∈ C ∧ ∀ j ∈ C, s j ≤ s b) → i ≤ b} := by
    ext s
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, amax,
      min'_eq_iff, mem_filter]
  rw [hset]
  have hle : ∀ a b : Fin n, Measurable (fun s : Fin n → ℝ => s a ≤ s b) := fun a b =>
    measurableSet_setOfPred.1 (measurableSet_le (measurable_pi_apply a) (measurable_pi_apply b))
  apply measurableSet_setOfPred.2
  apply Measurable.and
  · apply Measurable.and measurable_const
    exact Measurable.forall fun j => Measurable.imp measurable_const (hle j i)
  · exact Measurable.forall fun b => Measurable.imp
      (Measurable.and measurable_const
        (Measurable.forall fun j => Measurable.imp measurable_const (hle j b)))
      measurable_const

/-- The selector `amax`. -/
noncomputable def sel0 : Selector n T := fun _ C hC s => amax C hC s

lemma sel0_argmax : IsArgmaxSelector (sel0 : Selector n T) := fun _ C hC s => amax_spec C hC s

lemma offer_meas {γ : Type*} [MeasurableSpace γ] (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ)
    (t : Fin T) (q : Fin n → ℕ → ℝ) (A : Finset (Fin n)) (φ : Option (Fin n) → γ) :
    Measurable (fun W => φ (offer m r α (sel0 : Selector n T) t q W A)) := by
  by_cases h : A.Nonempty
  · have hfun : (fun W => φ (offer m r α (sel0 : Selector n T) t q W A)) =
        fun W => (fun x : (Fin n → ℝ) × Fin n =>
          if 0 < score m r α q x.1 x.2 then φ (some x.2) else φ none)
          (W, amax A h (score m r α q W)) := by
      funext W
      simp only [offer, dif_pos h, sel0]
      by_cases hh : 0 < score m r α q W (amax A h (score m r α q W)) <;> simp only [hh, if_true, if_false]
    rw [hfun]
    have hg : Measurable (fun x : (Fin n → ℝ) × Fin n =>
          if 0 < score m r α q x.1 x.2 then φ (some x.2) else φ none) := by
      apply measurable_from_prod_countable_left
      intro i
      dsimp only
      exact Measurable.ite (measurableSet_lt measurable_const (score_meas m r α q i))
        measurable_const measurable_const
    exact hg.comp (measurable_id.prodMk ((amax_meas A h).comp (scorevec_meas m r α q)))
  · simp only [offer, dif_neg h]
    exact measurable_const

lemma avail_meas (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ) (p : Fin T → Fin n → ℕ → ℝ)
    (present : Finset (Fin n)) :
    ∀ s, Measurable (fun W => availBefore m r α p (sel0 : Selector n T) present W s) := by
  intro s
  induction s with
  | zero => simp only [availBefore]; exact measurable_const
  | succ s ih =>
    by_cases hs : s < T
    · simp only [availBefore, dif_pos hs]
      have hstep : Measurable (fun x : (Fin n → ℝ) × Finset (Fin n) =>
          match offer m r α (sel0 : Selector n T) ⟨s, hs⟩ (p ⟨s, hs⟩) x.1 x.2 with
          | some i => x.2.erase i
          | none => x.2) := by
        apply measurable_from_prod_countable_left
        intro A
        exact offer_meas m r α ⟨s, hs⟩ (p ⟨s, hs⟩) A (fun o => match o with
          | some i => A.erase i
          | none => A)
      exact hstep.comp (measurable_id.prodMk ih)
    · simp only [availBefore, dif_neg hs]
      exact ih

lemma rev2_meas (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ) (p : Fin T → Fin n → ℕ → ℝ)
    (present : Finset (Fin n)) :
    Measurable (fun W => rev2 m r α p (sel0 : Selector n T) present W) := by
  unfold rev2
  apply Finset.measurable_sum
  intro t _
  have hstep : Measurable (fun x : (Fin n → ℝ) × Finset (Fin n) =>
      match offer m r α (sel0 : Selector n T) t (p t) x.1 x.2 with
      | some i => MultiPriceOnline.Balance.pr (r i) (jt m (p t) i)
      | none => 0) := by
    apply measurable_from_prod_countable_left
    intro A
    exact offer_meas m r α t (p t) A (fun o => match o with
      | some i => MultiPriceOnline.Balance.pr (r i) (jt m (p t) i)
      | none => 0)
  exact hstep.comp (measurable_id.prodMk (avail_meas m r α p present t.val))

/-! ### Agreement of argmax selectors when there are no ties -/

/-- No ties at all among distinct items. -/
def Good (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ) (p : Fin T → Fin n → ℕ → ℝ) (W : Fin n → ℝ) :
    Prop :=
  ∀ t (i i' : Fin n), i ≠ i' → score m r α (p t) W i ≠ score m r α (p t) W i'

lemma offer_congr (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ) (p : Fin T → Fin n → ℕ → ℝ)
    (sel sel' : Selector n T) (hs : IsArgmaxSelector sel) (hs' : IsArgmaxSelector sel')
    (W : Fin n → ℝ) (hG : Good m r α p W) (t : Fin T) (A : Finset (Fin n)) :
    offer m r α sel t (p t) W A = offer m r α sel' t (p t) W A := by
  unfold offer
  by_cases h : A.Nonempty
  · simp only [dif_pos h]
    set s := score m r α (p t) W
    obtain ⟨ha, hamax⟩ := hs t A h s
    obtain ⟨hb, hbmax⟩ := hs' t A h s
    have heq : s (sel t A h s) = s (sel' t A h s) :=
      le_antisymm (hbmax _ ha) (hamax _ hb)
    have hab : sel t A h s = sel' t A h s := by
      by_contra hne
      exact hG t _ _ hne heq
    rw [hab]
  · simp only [dif_neg h]

lemma avail_congr (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ) (p : Fin T → Fin n → ℕ → ℝ)
    (sel sel' : Selector n T) (hs : IsArgmaxSelector sel) (hs' : IsArgmaxSelector sel')
    (present : Finset (Fin n)) (W : Fin n → ℝ) (hG : Good m r α p W) :
    ∀ s, availBefore m r α p sel present W s = availBefore m r α p sel' present W s := by
  intro s
  induction s with
  | zero => simp only [availBefore]
  | succ s ih =>
    by_cases hT : s < T
    · simp only [availBefore, dif_pos hT]
      rw [ih, offer_congr m r α p sel sel' hs hs' W hG ⟨s, hT⟩]
    · simp only [availBefore, dif_neg hT]
      exact ih

lemma rev2_congr (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ) (p : Fin T → Fin n → ℕ → ℝ)
    (sel sel' : Selector n T) (hs : IsArgmaxSelector sel) (hs' : IsArgmaxSelector sel')
    (present : Finset (Fin n)) (W : Fin n → ℝ) (hG : Good m r α p W) :
    rev2 m r α p sel present W = rev2 m r α p sel' present W := by
  unfold rev2 run2
  apply Finset.sum_congr rfl
  intro t _
  rw [avail_congr m r α p sel sel' hs hs' present W hG,
    offer_congr m r α p sel sel' hs hs' W hG]

/-- Almost every seed vector has no ties. -/
lemma ae_good (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ)
    (hr : ∀ i, MultiPriceOnline.Ranking.IsPriceSet (m i) (r i))
    (hα : ∀ i, MultiPriceOnline.Balance.IsBookingLimits (m i) (r i) (α i))
    (p : Fin T → Fin n → ℕ → ℝ) :
    ∀ᵐ W ∂(seedMeasure n), Good m r α p W := by
  unfold Good
  rw [ae_all_iff]; intro t
  rw [ae_all_iff]; intro i
  rw [ae_all_iff]; intro i'
  by_cases hii : i = i'
  · exact Filter.Eventually.of_forall fun _ h => absurd hii h
  · rw [ae_iff]
    set ci := MultiPriceOnline.Balance.pr (r i) (jt m (p t) i)
    set ci' := MultiPriceOnline.Balance.pr (r i') (jt m (p t) i')
    have hset : {W : Fin n → ℝ | ¬(i ≠ i' → score m r α (p t) W i ≠ score m r α (p t) W i')} =
        {W | Phi (m i) (r i) (α i) (W i) =
          (fun y => Phi (m i') (r i') (α i') y + (ci - ci')) (W i')} := by
      ext W
      simp only [Set.mem_ofPred_eq, score, ne_eq, Classical.not_imp, not_not]
      constructor
      · rintro ⟨-, h⟩; linarith
      · intro h; exact ⟨hii, by linarith⟩
    rw [hset]
    unfold seedMeasure
    apply null_pair _ hii (Phi_meas _ _ _) ((Phi_meas _ _ _).add measurable_const)
    intro c
    exact nonpos_iff_eq_zero.1 ((Measure.restrict_apply_le _ _).trans
      (le_of_eq (Phi_level_null (hr i) (hα i) c)))

lemma ae_Icc (n : ℕ) : ∀ᵐ W ∂(seedMeasure n), ∀ i, W i ∈ Set.Icc (0 : ℝ) 1 := by
  rw [ae_all_iff]
  intro i
  unfold seedMeasure
  exact (Measure.tendsto_eval_ae_ae (i := i)).eventually (ae_restrict_mem measurableSet_Icc)

instance seed_finite (n : ℕ) : IsFiniteMeasure (seedMeasure n) := by
  unfold seedMeasure; infer_instance

lemma rev2_integrable (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ)
    (hr : ∀ i, MultiPriceOnline.Ranking.IsPriceSet (m i) (r i))
    (hα : ∀ i, MultiPriceOnline.Balance.IsBookingLimits (m i) (r i) (α i))
    (p : Fin T → Fin n → ℕ → ℝ) (sel : Selector n T) (hsel : IsArgmaxSelector sel) :
    Integrable (fun W => rev2 m r α p sel Finset.univ W) (seedMeasure n) := by
  have hae : (fun W => rev2 m r α p (sel0 : Selector n T) Finset.univ W) =ᵐ[seedMeasure n]
      (fun W => rev2 m r α p sel Finset.univ W) := by
    filter_upwards [ae_good m r α hr hα p] with W hW
    exact rev2_congr m r α p sel0 sel sel0_argmax hsel _ W hW
  refine Integrable.of_bound
    (((rev2_meas m r α p Finset.univ).aestronglyMeasurable).congr hae)
    (∑ t : Fin T, ∑ i : Fin n, |MultiPriceOnline.Balance.pr (r i) (jt m (p t) i)|)
    (Filter.Eventually.of_forall fun W => ?_)
  unfold rev2
  rw [Real.norm_eq_abs]
  refine (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t _ => ?_)
  rcases run2 m r α p sel Finset.univ W t with _ | i
  · simp only [abs_zero]
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  · exact Finset.single_le_sum (f := fun i => |MultiPriceOnline.Balance.pr (r i) (jt m (p t) i)|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ i)

/-! ### Structure of a run -/

lemma offer_some {m : Fin n → ℕ} {r α : Fin n → ℕ → ℝ} {sel : Selector n T}
    (hsel : IsArgmaxSelector sel) {t : Fin T} {q : Fin n → ℕ → ℝ} {W : Fin n → ℝ}
    {A : Finset (Fin n)} {i : Fin n} (h : offer m r α sel t q W A = some i) :
    i ∈ A ∧ 0 < score m r α q W i := by
  unfold offer at h
  split_ifs at h with h1 h2
  have h' := Option.some.inj h
  subst h'
  exact ⟨(hsel t A h1 _).1, h2⟩

lemma avail_succ_sub (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ) (p : Fin T → Fin n → ℕ → ℝ)
    (sel : Selector n T) (present : Finset (Fin n)) (W : Fin n → ℝ) (s : ℕ) :
    availBefore m r α p sel present W (s + 1) ⊆ availBefore m r α p sel present W s := by
  simp only [availBefore]
  split_ifs with hs
  · split
    · exact Finset.erase_subset _ _
    · exact subset_refl _
  · exact subset_refl _

lemma avail_anti (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ) (p : Fin T → Fin n → ℕ → ℝ)
    (sel : Selector n T) (present : Finset (Fin n)) (W : Fin n → ℝ) (s : ℕ) :
    ∀ k, availBefore m r α p sel present W (s + k) ⊆ availBefore m r α p sel present W s := by
  intro k
  induction k with
  | zero => exact subset_refl _
  | succ k ih => exact (avail_succ_sub m r α p sel present W (s + k)).trans ih

lemma run2_not_mem_succ {m : Fin n → ℕ} {r α : Fin n → ℕ → ℝ} {p : Fin T → Fin n → ℕ → ℝ}
    {sel : Selector n T} {present : Finset (Fin n)} {W : Fin n → ℝ} {s : Fin T} {i : Fin n}
    (h : run2 m r α p sel present W s = some i) :
    i ∉ availBefore m r α p sel present W (s.val + 1) := by
  unfold run2 at h
  simp only [availBefore, dif_pos s.isLt, Fin.eta, h]
  exact Finset.notMem_erase _ _

lemma run2_unique {m : Fin n → ℕ} {r α : Fin n → ℕ → ℝ} {p : Fin T → Fin n → ℕ → ℝ}
    {sel : Selector n T} (hsel : IsArgmaxSelector sel) {present : Finset (Fin n)}
    {W : Fin n → ℝ} {s t : Fin T} {i : Fin n}
    (hs : run2 m r α p sel present W s = some i) (ht : run2 m r α p sel present W t = some i) :
    s = t := by
  have key : ∀ s t : Fin T, s < t → run2 m r α p sel present W s = some i →
      run2 m r α p sel present W t = some i → False := by
    intro s t hlt hs ht
    have hmem := (offer_some hsel ht).1
    have hsub := avail_anti m r α p sel present W (s.val + 1) (t.val - (s.val + 1))
    have heq : s.val + 1 + (t.val - (s.val + 1)) = t.val := by
      have : s.val < t.val := hlt
      omega
    rw [heq] at hsub
    exact run2_not_mem_succ hs (hsub hmem)
  rcases lt_trichotomy s t with h | h | h
  · exact (key s t h hs ht).elim
  · exact h
  · exact (key t s h ht hs).elim

lemma sumY_eq (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ) (p : Fin T → Fin n → ℕ → ℝ)
    (sel : Selector n T) (hsel : IsArgmaxSelector sel) (W : Fin n → ℝ) :
    ∑ i, Yi m r α p sel Finset.univ W i =
      ∑ t, (match run2 m r α p sel Finset.univ W t with
        | some i => Yi m r α p sel Finset.univ W i
        | none => 0) := by
  have h1 : ∀ t, (match run2 m r α p sel Finset.univ W t with
        | some i => Yi m r α p sel Finset.univ W i
        | none => 0) = ∑ i, if run2 m r α p sel Finset.univ W t = some i then
          Yi m r α p sel Finset.univ W i else 0 := by
    intro t
    rcases run2 m r α p sel Finset.univ W t with _ | i0
    · simp
    · simp
  rw [Finset.sum_congr rfl fun t _ => h1 t, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hex : ∃ t, run2 m r α p sel Finset.univ W t = some i
  · obtain ⟨t0, ht0⟩ := hex
    rw [Finset.sum_eq_single t0]
    · simp [ht0]
    · intro b _ hb
      rw [if_neg]
      intro hb'
      exact hb (run2_unique hsel hb' ht0)
    · intro h; exact absurd (Finset.mem_univ _) h
  · push_neg at hex
    simp [hex, Yi]

lemma Yi_nonneg (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ)
    (hr : ∀ i, MultiPriceOnline.Ranking.IsPriceSet (m i) (r i))
    (hα : ∀ i, MultiPriceOnline.Balance.IsBookingLimits (m i) (r i) (α i))
    (p : Fin T → Fin n → ℕ → ℝ) (sel : Selector n T) (W : Fin n → ℝ) (i : Fin n) :
    0 ≤ Yi m r α p sel Finset.univ W i := by
  unfold Yi
  split_ifs
  · exact PhiDeriv_nonneg (hr i) (hα i) _
  · exact le_rfl

lemma Zt_nonneg (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ)
    (p : Fin T → Fin n → ℕ → ℝ) (sel : Selector n T) (hsel : IsArgmaxSelector sel)
    (W : Fin n → ℝ) (t : Fin T) :
    0 ≤ Zt m r α p sel Finset.univ W t := by
  unfold Zt
  rcases h : run2 m r α p sel Finset.univ W t with _ | i
  · exact le_rfl
  · unfold run2 at h
    exact (offer_some hsel h).2.le

lemma pointwise (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ)
    (hr : ∀ i, MultiPriceOnline.Ranking.IsPriceSet (m i) (r i))
    (hα : ∀ i, MultiPriceOnline.Balance.IsBookingLimits (m i) (r i) (α i))
    (p : Fin T → Fin n → ℕ → ℝ) (hp : IsDeterministic m p)
    (sel : Selector n T) (hsel : IsArgmaxSelector sel)
    (Fm : ℝ) (hFm : ∀ i, Fm ≤ F (α i))
    (W : Fin n → ℝ) (hW : ∀ i, W i ∈ Set.Icc (0 : ℝ) 1) :
    Fm * (∑ i, Yi m r α p sel Finset.univ W i + ∑ t, Zt m r α p sel Finset.univ W t) ≤
      rev2 m r α p sel Finset.univ W := by
  rw [sumY_eq m r α p sel hsel W, ← Finset.sum_add_distrib, Finset.mul_sum]
  unfold rev2
  apply Finset.sum_le_sum
  intro t _
  have hZ := Zt_nonneg m r α p sel hsel W t
  have h2 : ∀ i, run2 m r α p sel Finset.univ W t = some i →
      Fm * (Yi m r α p sel Finset.univ W i + Zt m r α p sel Finset.univ W t) ≤
        MultiPriceOnline.Balance.pr (r i) (jt m (p t) i) := by
    intro i hi
    have hl := MultiPriceOnline.Ranking.lemma_2 m r α hr hα p hp sel hsel W hW i t hi
    have hY := Yi_nonneg m r α hr hα p sel W i
    have hFi : Fm ≤ 1 - Real.exp (-α i 1) := hFm i
    nlinarith
  have hZ0 : run2 m r α p sel Finset.univ W t = none → Zt m r α p sel Finset.univ W t = 0 := by
    intro h; unfold Zt; rw [h]
  rcases h : run2 m r α p sel Finset.univ W t with _ | i
  · simp [hZ0 h]
  · exact h2 i h

end MPR2Aux

open MPR2Aux in
theorem solution {n T : ℕ} (hn : 0 < n) (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ)
    (hr : ∀ i, MultiPriceOnline.Ranking.IsPriceSet (m i) (r i))
    (hα : ∀ i, MultiPriceOnline.Balance.IsBookingLimits (m i) (r i) (α i))
    (p : Fin T → Fin n → ℕ → ℝ) (hp : IsDeterministic m p)
    (sel : Selector n T) (hsel : IsArgmaxSelector sel)
    (x : Fin T → Fin n → ℕ → ℝ) (hx : LPFeasible (fun _ => 1) m p x) :
    (Finset.univ.inf' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ fun i => F (α i)) * lpObj m r p x ≤
      ∫ W, rev2 m r α p sel Finset.univ W ∂(seedMeasure n) := by
  set S := seedMeasure n with hS
  set Fm := (Finset.univ.inf' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ fun i => F (α i)) with hFmdef
  have hFm : ∀ i, Fm ≤ F (α i) := fun i => Finset.inf'_le _ (Finset.mem_univ i)
  have hFm0 : 0 ≤ Fm := by
    apply Finset.le_inf'
    intro i _
    show 0 ≤ 1 - Real.exp (-α i 1)
    have h1 : 0 < α i 1 := (hα i).1 1 le_rfl (hr i).1
    have : Real.exp (-α i 1) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hp01 : ∀ t i j, 1 ≤ j → j ≤ m i → 0 ≤ p t i j ∧ p t i j ≤ 1 := by
    intro t i j h1 h2
    rcases hp t i j h1 h2 with h | h <;> rw [h] <;> norm_num
  have hdual := MultiPriceOnline.Ranking.lemma_3 m r α hr hα p hp sel hsel
  have hwd := MultiPriceOnline.Ranking.weak_duality (fun _ => 1) m r p hp01 x hx _ _ hdual
  simp only [dualObj, Nat.cast_one, one_mul] at hwd
  set Yf : Fin n → (Fin n → ℝ) → ℝ := fun i W => Yi m r α p sel Finset.univ W i with hYf
  set Zf : Fin T → (Fin n → ℝ) → ℝ := fun t W => Zt m r α p sel Finset.univ W t with hZf
  classical
  let Y' : Fin n → (Fin n → ℝ) → ℝ := fun i => if Integrable (Yf i) S then Yf i else 0
  let Z' : Fin T → (Fin n → ℝ) → ℝ := fun t => if Integrable (Zf t) S then Zf t else 0
  have hY'int : ∀ i, Integrable (Y' i) S := by
    intro i; by_cases h : Integrable (Yf i) S
    · simp only [Y', if_pos h]; exact h
    · simp only [Y', if_neg h]; exact integrable_zero _ _ _
  have hZ'int : ∀ t, Integrable (Z' t) S := by
    intro t; by_cases h : Integrable (Zf t) S
    · simp only [Z', if_pos h]; exact h
    · simp only [Z', if_neg h]; exact integrable_zero _ _ _
  have hY'eq : ∀ i, ∫ W, Y' i W ∂S = ∫ W, Yf i W ∂S := by
    intro i; by_cases h : Integrable (Yf i) S
    · simp only [Y', if_pos h]
    · simp only [Y', if_neg h, Pi.zero_apply, integral_zero]; rw [integral_undef h]
  have hZ'eq : ∀ t, ∫ W, Z' t W ∂S = ∫ W, Zf t W ∂S := by
    intro t; by_cases h : Integrable (Zf t) S
    · simp only [Z', if_pos h]
    · simp only [Z', if_neg h, Pi.zero_apply, integral_zero]; rw [integral_undef h]
  have hY'le : ∀ i W, Y' i W ≤ Yf i W := by
    intro i W; by_cases h : Integrable (Yf i) S
    · simp only [Y', if_pos h, le_refl]
    · simp only [Y', if_neg h, Pi.zero_apply]; exact Yi_nonneg m r α hr hα p sel W i
  have hZ'le : ∀ t W, Z' t W ≤ Zf t W := by
    intro t W; by_cases h : Integrable (Zf t) S
    · simp only [Z', if_pos h, le_refl]
    · simp only [Z', if_neg h, Pi.zero_apply]; exact Zt_nonneg m r α p sel hsel W t
  have hrev := rev2_integrable m r α hr hα p sel hsel
  have hint : Integrable (fun W => Fm * (∑ i, Y' i W + ∑ t, Z' t W)) S :=
    ((integrable_finset_sum _ fun i _ => hY'int i).add
      (integrable_finset_sum _ fun t _ => hZ'int t)).const_mul Fm
  have hae : (fun W => Fm * (∑ i, Y' i W + ∑ t, Z' t W)) ≤ᵐ[S]
      (fun W => rev2 m r α p sel Finset.univ W) := by
    filter_upwards [ae_Icc n] with W hW
    refine le_trans ?_ (pointwise m r α hr hα p hp sel hsel Fm hFm W hW)
    apply mul_le_mul_of_nonneg_left _ hFm0
    exact add_le_add (Finset.sum_le_sum fun i _ => hY'le i W)
      (Finset.sum_le_sum fun t _ => hZ'le t W)
  calc Fm * lpObj m r p x
      ≤ Fm * (∑ i, ∫ W, Yf i W ∂S + ∑ t, ∫ W, Zf t W ∂S) :=
        mul_le_mul_of_nonneg_left hwd hFm0
    _ = ∫ W, Fm * (∑ i, Y' i W + ∑ t, Z' t W) ∂S := by
        rw [integral_const_mul, integral_add (integrable_finset_sum _ fun i _ => hY'int i)
          (integrable_finset_sum _ fun t _ => hZ'int t), integral_finset_sum _ fun i _ => hY'int i,
          integral_finset_sum _ fun t _ => hZ'int t]
        simp only [hY'eq, hZ'eq]
    _ ≤ ∫ W, rev2 m r α p sel Finset.univ W ∂S := integral_mono_ae hint hrev hae
