-- Prove2me | solution 1 for KWSpectrum.Estimator.highest_weight
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T01:19:24.797342+00:00
-- url     : https://prove2.me/submissions/d155d2fb-82d9-4b9b-8d36-77dfcd709277

import Mathlib
import Definitions.Def_KWSpectrum_Estimator_Model

open QAlgorithms QAlgorithms.Schur KWSpectrum.Estimator

lemma kw_card_filter_subtype (s : Finset (ℕ × ℕ)) (p : ℕ × ℕ → Prop) [DecidablePred p] :
    (Finset.univ.filter fun a : s => p a.val).card = (s.filter p).card := by
  rw [← Finset.card_map (Function.Embedding.subtype _)]
  congr 1
  ext x
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.coe_subtype, Subtype.exists, exists_and_right, exists_eq_right]
  constructor
  · rintro ⟨h2, h1⟩; exact ⟨h2, h1⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2⟩

lemma kw_row_lt {d N : ℕ} (Y : Partition d N) (a : Y.val.cells) : a.val.1 < d := by
  have h' : (a.val.1, a.val.2) ∈ Y.val := a.property
  have h0 : (a.val.1, 0) ∈ Y.val :=
    Y.val.up_left_mem le_rfl (Nat.zero_le _) h'
  exact lt_of_lt_of_le (YoungDiagram.mem_iff_lt_colLen.mp h0) Y.property.2

/-- the row of a cell, as an element of `Fin d` -/
def kwRowF {d N : ℕ} (Y : Partition d N) (a : Y.val.cells) : Fin d :=
  ⟨a.val.1, kw_row_lt Y a⟩

lemma kw_card_row {d N : ℕ} (Y : Partition d N) (i : ℕ) :
    (Finset.univ.filter fun a : Y.val.cells => a.val.1 = i).card = Y.val.rowLen i := by
  rw [kw_card_filter_subtype Y.val.cells (fun c => c.1 = i), YoungDiagram.rowLen_eq_card]
  rfl

lemma kw_sum_rowLen {d N : ℕ} (Y : Partition d N) (k : ℕ) :
    ∑ i : Fin d with i.val < k, Y.val.rowLen i.val =
      (Finset.univ.filter fun a : Y.val.cells => a.val.1 < k).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := kwRowF Y)
    (t := Finset.univ.filter fun i : Fin d => i.val < k)]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_filter] at hi
    rw [← kw_card_row Y i.val, Finset.filter_filter]
    congr 1
    apply Finset.filter_congr
    intro a _
    constructor
    · intro h; exact ⟨by rw [h]; exact hi.2, Fin.ext h⟩
    · intro h; exact Fin.ext_iff.mp h.2
  · intro a ha
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha ⊢
    exact ha

lemma kw_sum_content {d N : ℕ} (Y : Partition d N) (T : Y.val.cells → Fin d) (k : ℕ) :
    ∑ i : Fin d with i.val < k, content Y T i =
      (Finset.univ.filter fun a : Y.val.cells => (T a).val < k).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := T)
    (t := Finset.univ.filter fun i : Fin d => i.val < k)]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_filter] at hi
    unfold content
    rw [Finset.filter_filter]
    congr 1
    apply Finset.filter_congr
    intro a _
    constructor
    · intro h; exact ⟨by rw [h]; exact hi.2, h⟩
    · intro h; exact h.2
  · intro a ha
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha ⊢
    exact ha

lemma kw_T_ge {d N : ℕ} (Y : Partition d N) (T : Y.val.cells → Fin d)
    (hT : IsSemistandardFilling Y T) : ∀ a : Y.val.cells, a.val.1 ≤ (T a).val := by
  suffices h : ∀ n, ∀ a : Y.val.cells, a.val.1 = n → n ≤ (T a).val from
    fun a => h _ a rfl
  intro n
  induction n with
  | zero => intro a _; exact Nat.zero_le _
  | succ n ih =>
    intro a ha
    have hmem : (n, a.val.2) ∈ Y.val.cells := by
      have h' : (a.val.1, a.val.2) ∈ Y.val := a.property
      exact Y.val.up_left_mem (by omega) le_rfl h'
    let b : Y.val.cells := ⟨(n, a.val.2), hmem⟩
    have hb := ih b rfl
    have hlt := (hT b a).2 rfl (by simp [b]; omega)
    have : (T b).val < (T a).val := hlt
    omega

theorem solution {d N : ℕ} (Y : Partition d N) :
    (∃! T : Y.val.cells → Fin d,
      IsSemistandardFilling Y T ∧ content Y T = fun i => Y.val.rowLen i.val) ∧
    ∀ T : Y.val.cells → Fin d, IsSemistandardFilling Y T →
      (∀ k : ℕ, ∑ i : Fin d with i.val < k, content Y T i ≤
          ∑ i : Fin d with i.val < k, Y.val.rowLen i.val) ∧
      ∑ i : Fin d, content Y T i = ∑ i : Fin d, Y.val.rowLen i.val := by
  have hdom : ∀ T : Y.val.cells → Fin d, IsSemistandardFilling Y T → ∀ k : ℕ,
      (Finset.univ.filter fun a : Y.val.cells => (T a).val < k) ⊆
        (Finset.univ.filter fun a : Y.val.cells => a.val.1 < k) := by
    intro T hT k a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact lt_of_le_of_lt (kw_T_ge Y T hT a) ha
  refine ⟨⟨kwRowF Y, ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro a b
    refine ⟨fun h _ => ?_, fun _ h => ?_⟩
    · exact le_of_eq (Fin.ext h)
    · exact h
  · funext i
    unfold content
    rw [← kw_card_row Y i.val]
    congr 1
    apply Finset.filter_congr
    intro a _
    simp [kwRowF, Fin.ext_iff]
  · rintro T ⟨hT, hc⟩
    funext a
    apply Fin.ext
    apply le_antisymm _ (kw_T_ge Y T hT a)
    have hsub := hdom T hT (a.val.1 + 1)
    have hcard : (Finset.univ.filter fun b : Y.val.cells => b.val.1 < a.val.1 + 1).card ≤
        (Finset.univ.filter fun b : Y.val.cells => (T b).val < a.val.1 + 1).card := by
      rw [← kw_sum_content, ← kw_sum_rowLen, hc]
    have heq := Finset.eq_of_subset_of_card_le hsub hcard
    have ha : a ∈ (Finset.univ.filter fun b : Y.val.cells => b.val.1 < a.val.1 + 1) := by
      simp
    rw [← heq] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    show (T a).val ≤ a.val.1
    omega
  · intro T hT
    have hle : ∀ k : ℕ, ∑ i : Fin d with i.val < k, content Y T i ≤
        ∑ i : Fin d with i.val < k, Y.val.rowLen i.val := by
      intro k
      rw [kw_sum_content, kw_sum_rowLen]
      exact Finset.card_le_card (hdom T hT k)
    refine ⟨hle, ?_⟩
    have h1 := kw_sum_content Y T d
    have h2 := kw_sum_rowLen Y d
    have hf : (Finset.univ.filter fun i : Fin d => i.val < d) = Finset.univ :=
      Finset.filter_true_of_mem fun i _ => i.isLt
    rw [hf] at h1 h2
    rw [h1, h2]
    congr 1
    rw [Finset.filter_true_of_mem fun a _ => (T a).isLt,
      Finset.filter_true_of_mem fun a _ => kw_row_lt Y a]
