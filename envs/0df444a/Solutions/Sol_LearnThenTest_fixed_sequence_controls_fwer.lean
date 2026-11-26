-- Prove2me | solution 1 for LearnThenTest.fixed_sequence_controls_fwer
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T21:51:23.582805+00:00
-- url     : https://prove2.me/submissions/f71ee06f-aab2-469a-93fb-d00916eaa590

import Mathlib
import Definitions.Def_LearnThenTest_Basic

open MeasureTheory ProbabilityTheory Filter
namespace LearnThenTest

theorem _root_.solution (N : ℕ) (δ : ℝ) (hδ : 0 < δ ∧ δ < 1)
    (J : Finset (Fin N)) : IsFWERControlling N δ (fixedSeq N δ J) := by
  have hmem : ∀ (thr : ℝ) (x : Fin N → ℝ) (i : Fin N), i ∈ fixedSeq N δ J x → ∃ j ∈ J, i ∈ fixedSeqChain (δ / J.card) x j := by
    intro _ x i hi
    unfold fixedSeq at hi
    have gen : ∀ (l : List (Fin N)) (S : Finset (Fin N)),
        i ∈ l.foldl (fun S j => if j ∈ S then S else S ∪ fixedSeqChain (δ / J.card) x j) S →
        i ∈ S ∨ ∃ j ∈ l, i ∈ fixedSeqChain (δ / J.card) x j := by
      intro l
      induction l with
      | nil => intro S h; exact Or.inl h
      | cons a l ih =>
        intro S h
        rw [List.foldl_cons] at h
        rcases ih _ h with h' | ⟨j, hj, h'⟩
        · split_ifs at h' with ha
          · exact Or.inl h'
          · rcases Finset.mem_union.1 h' with h'' | h''
            · exact Or.inl h''
            · exact Or.inr ⟨a, List.mem_cons_self, h''⟩
        · exact Or.inr ⟨j, List.mem_cons_of_mem _ hj, h'⟩
    rcases gen _ _ hi with h | ⟨j, hj, h⟩
    · simp at h
    · exact ⟨j, (Finset.mem_sort _).1 hj, h⟩
  have hchain : ∀ (j i : Fin N), MeasurableSet {x : Fin N → ℝ | i ∈ fixedSeqChain (δ / J.card) x j} := by
    intro j i
    have : {x : Fin N → ℝ | i ∈ fixedSeqChain (δ / J.card) x j}
        = {x | j ≤ i ∧ ∀ k : Fin N, j ≤ k → k ≤ i → x k ≤ δ / J.card} := by
      ext x; simp [fixedSeqChain]
    rw [this]
    refine (MeasurableSet.const _).inter ?_
    have e : {x : Fin N → ℝ | ∀ k : Fin N, j ≤ k → k ≤ i → x k ≤ δ / J.card}
        = ⋂ k, ⋂ _ : j ≤ k, ⋂ _ : k ≤ i, {x : Fin N → ℝ | x k ≤ δ / J.card} := by
      ext x; simp
    refine (congrArg MeasurableSet e).mpr ?_
    exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
      measurableSet_le (measurable_pi_apply k) measurable_const
  refine ⟨fun i => ?_, fun μ hμ J0 hsupp hval => ?_⟩
  · have gen : ∀ (l : List (Fin N)) (S : (Fin N → ℝ) → Finset (Fin N)),
        (∀ i, MeasurableSet {x | i ∈ S x}) → ∀ i, MeasurableSet {x : Fin N → ℝ | i ∈ l.foldl (fun T j => if j ∈ T then T else T ∪ fixedSeqChain (δ / J.card) x j) (S x)} := by
      intro l
      induction l with
      | nil => intro S hS i; exact hS i
      | cons a l ih =>
        intro S hS i
        simp only [List.foldl_cons]
        refine ih (fun x => if a ∈ S x then S x else S x ∪ fixedSeqChain (δ / J.card) x a) (fun k => ?_) i
        have : {x | k ∈ (if a ∈ S x then S x else S x ∪ fixedSeqChain (δ / J.card) x a)}
            = {x | k ∈ S x} ∪ ({x | a ∈ S x}ᶜ ∩ {x | k ∈ fixedSeqChain (δ / J.card) x a}) := by
          ext x
          by_cases h : a ∈ S x <;> simp [h]
        rw [this]
        exact (hS k).union ((hS a).compl.inter (hchain a k))
    exact gen _ (fun _ => ∅) (fun i => by simp) i
  · classical
    set B : Set (Fin N → ℝ) := ⋃ j ∈ J, {x | ∃ h : (J0.filter (fun k => j ≤ k)).Nonempty,
      x ((J0.filter (fun k => j ≤ k)).min' h) ≤ δ / J.card} with hB
    have hpiece : ∀ j : Fin N, MeasurableSet {x : Fin N → ℝ | ∃ h : (J0.filter (fun k => j ≤ k)).Nonempty,
        x ((J0.filter (fun k => j ≤ k)).min' h) ≤ δ / J.card} := by
      intro j
      by_cases h : (J0.filter (fun k => j ≤ k)).Nonempty
      · simp only [h, exists_true_left]
        exact measurableSet_le (measurable_pi_apply _) measurable_const
      · simp [h]
    have hBm : MeasurableSet B := Finset.measurableSet_biUnion _ fun j _ => hpiece j
    have hsub : Bᶜ ⊆ {x | fixedSeq N δ J x ⊆ J0ᶜ} := by
      intro x hx i hi
      rw [Finset.mem_compl]
      intro hi0
      apply hx
      obtain ⟨j, hj, hc⟩ := hmem 0 x i hi
      rw [fixedSeqChain, Finset.mem_filter] at hc
      obtain ⟨-, hji, hall⟩ := hc
      rw [hB]
      simp only [Set.mem_iUnion]
      have hne : (J0.filter (fun k => j ≤ k)).Nonempty := ⟨i, Finset.mem_filter.2 ⟨hi0, hji⟩⟩
      refine ⟨j, hj, hne, ?_⟩
      have h1 := Finset.min'_mem _ hne
      rw [Finset.mem_filter] at h1
      exact hall _ h1.2 (Finset.min'_le _ _ (Finset.mem_filter.2 ⟨hi0, hji⟩))
    have hμB : μ B ≤ ENNReal.ofReal δ := by
      have h1 : μ B ≤ ∑ j ∈ J, ENNReal.ofReal (δ / J.card) := by
        refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
        have hc : (1:ℝ) ≤ J.card := by exact_mod_cast Finset.card_pos.2 ⟨j, hj⟩
        by_cases h : (J0.filter (fun k => j ≤ k)).Nonempty
        · have hm := Finset.min'_mem _ h
          rw [Finset.mem_filter] at hm
          have hd : δ / J.card ∈ Set.Icc (0:ℝ) 1 :=
            ⟨div_nonneg hδ.1.le (by positivity), by rw [div_le_one (by linarith)]; linarith [hδ.2]⟩
          refine le_trans (measure_mono ?_) (hval _ hm.1 _ hd)
          rintro x ⟨_, hx⟩; exact hx
        · simp [h]
      refine h1.trans ?_
      rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      rcases Nat.eq_zero_or_pos J.card with h | h
      · rw [h]; simp; exact hδ.1.le
      · have : (J.card:ℝ) ≠ 0 := by positivity
        rw [mul_div_cancel₀ _ this]
    refine le_trans ?_ (measure_mono hsub)
    rw [prob_compl_eq_one_sub hBm, ENNReal.ofReal_sub _ hδ.1.le, ENNReal.ofReal_one]
    exact tsub_le_tsub_left hμB 1


end LearnThenTest
