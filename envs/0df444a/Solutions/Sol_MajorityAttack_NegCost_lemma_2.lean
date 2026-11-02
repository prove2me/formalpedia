-- Prove2me | solution 1 for MajorityAttack.NegCost.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T22:41:14.057187+00:00
-- url     : https://prove2.me/submissions/d5ac448f-fcd8-468d-95e5-a6e0aef38b6a

import Mathlib
import Definitions.Def_MajorityAttack_NegCost_Fees

open MeasureTheory MajorityAttack.NegCost

namespace NegCostLemma2

lemma topFees_nonneg (b : ℕ) {n : ℕ} (φ : Fin n → ℝ) : 0 ≤ topFees b φ := by
  unfold topFees
  have hmem : (∅ : Finset (Fin n)) ∈
      (Finset.univ : Finset (Finset (Fin n))).filter (fun s => s.card ≤ b) := by simp
  simpa using Finset.le_sup' (fun s => ∑ t ∈ s, φ t) hmem

lemma le_topFees (b : ℕ) {n : ℕ} (φ : Fin n → ℝ) (s : Finset (Fin n)) (hs : s.card ≤ b) :
    ∑ t ∈ s, φ t ≤ topFees b φ := by
  unfold topFees
  exact Finset.le_sup' (fun s => ∑ t ∈ s, φ t) (by simp [hs])

lemma exists_topFees (b : ℕ) {n : ℕ} (φ : Fin n → ℝ) :
    ∃ s : Finset (Fin n), s.card ≤ b ∧ topFees b φ = ∑ t ∈ s, φ t := by
  unfold topFees
  obtain ⟨s, hs, h⟩ := Finset.exists_mem_eq_sup'
    (⟨∅, by simp⟩ : ((Finset.univ : Finset (Finset (Fin n))).filter
      (fun s => s.card ≤ b)).Nonempty) (fun s => ∑ t ∈ s, φ t)
  exact ⟨s, by simpa using hs, h⟩

lemma topFees_le_abs (b : ℕ) {n : ℕ} (φ : Fin n → ℝ) : topFees b φ ≤ ∑ t, |φ t| := by
  obtain ⟨s, -, h⟩ := exists_topFees b φ
  rw [h]
  calc ∑ t ∈ s, φ t ≤ ∑ t ∈ s, |φ t| := Finset.sum_le_sum (fun t _ => le_abs_self _)
    _ ≤ ∑ t, |φ t| := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => abs_nonneg _)

lemma measurable_topFees (b n : ℕ) : Measurable (fun φ : Fin n → ℝ => topFees b φ) := by
  unfold topFees
  have := Finset.measurable_sup' (δ := Fin n → ℝ) (α := ℝ)
    (s := (Finset.univ : Finset (Finset (Fin n))).filter (fun s => s.card ≤ b)) ⟨∅, by simp⟩
    (f := fun s φ => ∑ t ∈ s, φ t) (fun s _ => by fun_prop)
  convert this using 1
  ext φ
  exact (Finset.sup'_apply _ _ φ).symm

lemma integrable_topFees (μ : Measure ℝ) (hμ : FeeLaw μ) (b n : ℕ) :
    Integrable (fun φ : Fin n → ℝ => topFees b φ) (Measure.pi fun _ : Fin n => μ) := by
  have := hμ.prob
  have hint : Integrable (fun x : ℝ => |x|) μ := hμ.integrable.abs
  have hsum : Integrable (fun φ : Fin n → ℝ => ∑ t, |φ t|) (Measure.pi fun _ : Fin n => μ) :=
    integrable_finsetSum _ (fun t _ => integrable_comp_eval (μ := fun _ : Fin n => μ)
      (i := t) (f := fun x : ℝ => |x|) hint)
  refine hsum.mono' (measurable_topFees b n).aestronglyMeasurable (Filter.Eventually.of_forall ?_)
  intro φ
  rw [Real.norm_eq_abs, abs_of_nonneg (topFees_nonneg b φ)]
  exact topFees_le_abs b φ

lemma not_ae_const (μ : Measure ℝ) (hμ : FeeLaw μ) (a : ℝ) : ¬ (∀ᵐ x ∂μ, x = a) := by
  intro h
  have := hμ.prob
  apply hμ.nondegenerate a
  have hnull : μ {x | ¬ x = a} = 0 := ae_iff.1 h
  ext s hs
  rw [Measure.dirac_apply' a hs]
  by_cases has : a ∈ s
  · rw [Set.indicator_of_mem has]
    have : μ sᶜ = 0 := measure_mono_null (fun x hx => by
      intro hxa; exact hx (hxa ▸ has)) hnull
    rw [prob_compl_eq_zero_iff hs] at this
    simp [this]
  · rw [Set.indicator_of_notMem has]
    exact measure_mono_null (fun x hx => by intro hxa; exact has (hxa ▸ hx)) hnull

lemma nondeg (μ : Measure ℝ) (hμ : FeeLaw μ) :
    μ (Set.Iic (∫ x, x ∂μ)) ≠ 0 ∧ μ (Set.Ioi (∫ x, x ∂μ)) ≠ 0 := by
  have := hμ.prob
  set a := ∫ x, x ∂μ with ha
  have hint : Integrable (fun x : ℝ => x) μ := hμ.integrable
  constructor
  · intro h0
    apply not_ae_const μ hμ a
    have hlt : ∀ᵐ x ∂μ, a < x := by
      rw [ae_iff]
      have : {x : ℝ | ¬ a < x} = Set.Iic a := by ext; simp
      rw [this]; exact h0
    have hnn : 0 ≤ᵐ[μ] (fun x => x - a) := hlt.mono (fun x hx => by simp; linarith)
    have hi : Integrable (fun x => x - a) μ := hint.sub (integrable_const a)
    have hz : ∫ x, (x - a) ∂μ = 0 := by
      rw [integral_sub hint (integrable_const a)]; simp [ha]
    have := (integral_eq_zero_iff_of_nonneg_ae hnn hi).1 hz
    exact this.mono (fun x hx => by simp at hx; linarith)
  · intro h0
    apply not_ae_const μ hμ a
    have hle : ∀ᵐ x ∂μ, x ≤ a := by
      rw [ae_iff]
      have : {x : ℝ | ¬ x ≤ a} = Set.Ioi a := by ext; simp
      rw [this]; exact h0
    have hnn : 0 ≤ᵐ[μ] (fun x => a - x) := hle.mono (fun x hx => by simp; linarith)
    have hi : Integrable (fun x => a - x) μ := (integrable_const a).sub hint
    have hz : ∫ x, (a - x) ∂μ = 0 := by
      rw [integral_sub (integrable_const a) hint]; simp [ha]
    have := (integral_eq_zero_iff_of_nonneg_ae hnn hi).1 hz
    exact this.mono (fun x hx => by simp at hx; linarith)

lemma step (μ : Measure ℝ) (hμ : FeeLaw μ) (b m : ℕ) (hb : 0 < b) :
    blockFees μ b m < blockFees μ b (m + 1) := by
  have := hμ.prob
  set P := Measure.pi (fun _ : Fin (m + 1) => μ) with hP
  let f : (Fin (m + 1) → ℝ) → (Fin m → ℝ) := fun φ j => φ (Fin.castSucc j)
  let F : (Fin (m + 1) → ℝ) → ℝ := fun φ => topFees b (f φ)
  let G : (Fin (m + 1) → ℝ) → ℝ := fun φ => topFees b φ
  have hmp : MeasurePreserving f P (Measure.pi fun _ : Fin m => μ) := by
    have h1 := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) (Fin.last m)
    have h2 := measurePreserving_snd (μ := μ) (ν := Measure.pi fun _ : Fin m => μ)
    have h3 := h2.comp h1
    convert h3 using 1
    ext φ j
    simp [f, MeasurableEquiv.piFinSuccAbove, Fin.removeNth, Fin.init]
  have hFint : ∫ φ, F φ ∂P = blockFees μ b m := by
    unfold blockFees
    rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable
      (measurable_topFees b m).aestronglyMeasurable]
  have hGint : ∫ φ, G φ ∂P = blockFees μ b (m + 1) := rfl
  have hG : Integrable G P := integrable_topFees μ hμ b (m + 1)
  have hFG : ∀ φ, F φ ≤ G φ := by
    intro φ
    obtain ⟨S, hS, hSe⟩ := exists_topFees b (f φ)
    simp only [F, G]
    rw [hSe]
    have := le_topFees b φ (S.map Fin.castSuccEmb) (by simpa using hS)
    simpa [f] using this
  have hF : Integrable F P := by
    refine hG.mono' ((measurable_topFees b m).comp hmp.measurable).aestronglyMeasurable
      (Filter.Eventually.of_forall ?_)
    intro φ
    rw [Real.norm_eq_abs, abs_of_nonneg (topFees_nonneg b _)]
    exact hFG φ
  -- the positive-probability event
  obtain ⟨hlow, hhigh⟩ := nondeg μ hμ
  set a := ∫ x, x ∂μ with ha
  have ha0 : 0 ≤ a := by
    by_contra hneg
    push Not at hneg
    apply hlow
    exact measure_mono_null (fun x hx => by
      simp only [Set.mem_Iic] at hx; simp only [Set.mem_Iio]; linarith) hμ.nonneg
  let E : Set (Fin (m + 1) → ℝ) :=
    Set.pi Set.univ (fun i => if i = Fin.last m then Set.Ioi a else Set.Iic a)
  have hE : P E ≠ 0 := by
    simp only [E, hP]
    rw [Measure.pi_pi]
    rw [Finset.prod_ne_zero_iff]
    intro i _
    split_ifs
    · exact hhigh
    · exact hlow
  have hstrict : ∀ φ ∈ E, F φ < G φ := by
    intro φ hφ
    simp only [E, Set.mem_pi, Set.mem_univ, true_implies] at hφ
    have hlast : a < φ (Fin.last m) := by
      have := hφ (Fin.last m); simpa using this
    have hcs : ∀ j : Fin m, φ (Fin.castSucc j) ≤ a := by
      intro j
      have := hφ (Fin.castSucc j)
      rw [if_neg (Fin.castSucc_lt_last j).ne] at this
      simpa using this
    obtain ⟨S, hS, hSe⟩ := exists_topFees b (f φ)
    simp only [F, G]
    rw [hSe]
    rcases S.eq_empty_or_nonempty with h | ⟨s, hs⟩
    · subst h
      have := le_topFees b φ {Fin.last m} (by simp; omega)
      simp at this ⊢
      linarith
    · let T : Finset (Fin (m + 1)) := insert (Fin.last m) ((S.erase s).map Fin.castSuccEmb)
      have hnot : Fin.last m ∉ (S.erase s).map Fin.castSuccEmb := by
        simp only [Finset.mem_map, Fin.coe_castSuccEmb, not_exists, not_and]
        intro x _ hx
        exact (Fin.castSucc_lt_last x).ne hx
      have hcard : T.card ≤ b := by
        simp only [T]
        rw [Finset.card_insert_of_notMem hnot, Finset.card_map,
          Finset.card_erase_of_mem hs]
        have := Finset.card_pos.2 ⟨s, hs⟩
        omega
      have hT := le_topFees b φ T hcard
      have hsumT : ∑ t ∈ T, φ t = φ (Fin.last m) + ∑ t ∈ S.erase s, φ (Fin.castSucc t) := by
        simp only [T]
        rw [Finset.sum_insert hnot, Finset.sum_map]
        rfl
      have hsumS : ∑ t ∈ S, f φ t = φ (Fin.castSucc s) + ∑ t ∈ S.erase s, φ (Fin.castSucc t) :=
        (Finset.add_sum_erase S (fun t => φ (Fin.castSucc t)) hs).symm
      rw [hsumS]
      have := hcs s
      linarith
  have hpos : 0 < ∫ φ, (G - F) φ ∂P := by
    rw [integral_pos_iff_support_of_nonneg_ae
      (Filter.Eventually.of_forall (fun φ => by simp; exact hFG φ)) (hG.sub hF)]
    apply lt_of_lt_of_le (pos_iff_ne_zero.2 hE)
    apply measure_mono
    intro φ hφ
    simp only [Function.mem_support]
    have := hstrict φ hφ
    exact (sub_pos.2 this).ne'
  simp only [Pi.sub_apply] at hpos
  rw [integral_sub hG hF, hFint, hGint] at hpos
  linarith

end NegCostLemma2

theorem solution (μ : MeasureTheory.Measure ℝ) (hμ : FeeLaw μ)
    (b n n' : ℕ) (hb : 0 < b) (hbn : b < n) (hnn' : n < n') :
    blockFees μ b n < blockFees μ b n' :=
  strictMono_nat_of_lt_succ (f := fun k => blockFees μ b k)
    (fun m => NegCostLemma2.step μ hμ b m hb) hnn'
