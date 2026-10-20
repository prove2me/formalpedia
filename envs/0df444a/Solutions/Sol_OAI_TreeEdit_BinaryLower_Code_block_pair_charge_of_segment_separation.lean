-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.Code.block_pair_charge_of_segment_separation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:29:31.989004+00:00
-- url     : https://prove2.me/submissions/5f024bd6-b225-427e-9a1f-cb59631784ad

import Mathlib
import Definitions.Def_BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Model
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeWords
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeGeometry
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectors
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectorRestrictions
import Definitions.Def_OAI_Combinatorics_BinaryEdit_WordFinite
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeInstantiation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeTags
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedGaps
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedNonsplit
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_LCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_BlockExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedRowLCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteSeparation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Branching
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteActivityBridge
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteFourier
import Definitions.Def_OAI_Combinatorics_BinaryEdit_ScalarCutsBool
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteCoordinates
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteWordDetection
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CheapTranslations
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Distortion
import Definitions.Def_OAI_Combinatorics_BinaryEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_BinaryEdit_ParameterImage
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteParameters
import Definitions.Def_OAI_Combinatorics_BinaryEdit_EncodedImage
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteFamilyTransfer
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CodeNumerics
import Definitions.Def_OAI_Combinatorics_BinaryEdit_RandomMatching
import Definitions.Def_OAI_Combinatorics_BinaryEdit_SegmentMatchingCount
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CodeUnionBound
import Definitions.Def_OAI_Combinatorics_BinaryEdit_SegmentCode
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CodeAdditive
import Definitions.Def_OAI_Combinatorics_BinaryEdit_MatchingSpanBudget
import Definitions.Def_OAI_Combinatorics_BinaryEdit_MatchingSegments
import Definitions.Def_OAI_Combinatorics_BinaryEdit_UnequalSegments

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.Code
theorem h49_sub_seg {α : Type*} (x : List α) {k : ℕ}
    (i : Fin k → Fin x.length) (hi : StrictMono i) (a p : ℕ)
    (hi_lo : ∀ t, a ≤ (i t : ℕ)) (hi_hi : ∀ t, (i t : ℕ) < a + p) :
    (List.ofFn (fun t => x.get (i t))).Sublist ((x.drop a).take p) := by
  rw [List.sublist_iff_exists_fin_orderEmbedding_get_eq]
  have hlen : ∀ t : Fin k, (i t : ℕ) - a < ((x.drop a).take p).length := by
    intro t; simp only [List.length_take, List.length_drop]
    have := (i t).2; have := hi_lo t; have := hi_hi t; omega
  refine ⟨OrderEmbedding.ofStrictMono
    (fun s : Fin (List.ofFn (fun t => x.get (i t))).length =>
      (⟨(i (Fin.cast (by simp) s) : ℕ) - a, hlen _⟩ : Fin ((x.drop a).take p).length)) ?_, ?_⟩
  · intro s1 s2 h
    simp only [Fin.lt_def]
    have h1 := hi (show Fin.cast (by simp) s1 < (Fin.cast (by simp) s2 : Fin k) from h)
    have := hi_lo (Fin.cast (by simp) s1); have := hi_lo (Fin.cast (by simp) s2)
    rw [Fin.lt_def] at h1; omega
  · intro s
    simp only [OrderEmbedding.coe_ofStrictMono, List.get_eq_getElem, List.getElem_ofFn,
      List.getElem_take, List.getElem_drop]
    congr 1
    have := hi_lo (Fin.cast (by simp) s)
    rw [Nat.add_sub_cancel' this]; rfl

theorem h49_ofFn_sub {α : Type*} {n m k : ℕ}
    (x : Fin n → α) (y : Fin m → α)
    (i : Fin k → Fin n) (j : Fin k → Fin m)
    (hi : StrictMono i) (hj : StrictMono j)
    (hlabel : ∀ t, x (i t) = y (j t))
    (S : Finset (Fin k)) (a b p q : ℕ)
    (hi_lo : ∀ t ∈ S, a ≤ (i t : ℕ)) (hi_hi : ∀ t ∈ S, (i t : ℕ) < a + p)
    (hj_lo : ∀ t ∈ S, b ≤ (j t : ℕ)) (hj_hi : ∀ t ∈ S, (j t : ℕ) < b + q) :
    ∃ z : List α, z.Sublist (((List.ofFn x).drop a).take p) ∧
      z.Sublist (((List.ofFn y).drop b).take q) ∧ z.length = S.card := by
  let e := S.orderEmbOfFin rfl
  let i' : Fin S.card → Fin (List.ofFn x).length := fun s => Fin.cast (by simp) (i (e s))
  let j' : Fin S.card → Fin (List.ofFn y).length := fun s => Fin.cast (by simp) (j (e s))
  have hi' : StrictMono i' := fun s1 s2 h => by
    have := hi (e.strictMono h); exact this
  have hj' : StrictMono j' := fun s1 s2 h => by
    have := hj (e.strictMono h); exact this
  have hmem : ∀ s, e s ∈ S := fun s => S.orderEmbOfFin_mem rfl s
  refine ⟨List.ofFn (fun t => (List.ofFn x).get (i' t)),
    h49_sub_seg (List.ofFn x) i' hi' a p (fun t => hi_lo _ (hmem t)) (fun t => hi_hi _ (hmem t)), ?_, by simp⟩
  have : (fun t => (List.ofFn x).get (i' t)) = (fun t => (List.ofFn y).get (j' t)) := by
    funext t; simp [i', j', hlabel]
  rw [this]
  exact h49_sub_seg (List.ofFn y) j' hj' b q (fun t => hj_lo _ (hmem t)) (fun t => hj_hi _ (hmem t))

theorem h49_window (lo hi0 hi1 P a : ℕ) (h1 : lo ≤ hi0) (h2 : hi0 ≤ hi1) (h3 : hi1 < lo + P)
    (ha : hi1 + 1 - hi0 ≤ a) (haP : a ≤ P) :
    ∃ i, lo ≤ i ∧ i + a ≤ lo + P ∧ i ≤ hi0 ∧ hi1 < i + a :=
  ⟨min hi0 (lo + P - a), by omega, by omega, by omega, by omega⟩

theorem solution
    {α : Type*} {r M P : ℕ} (hP : 0 < P)
    (x y : Fin (M * P) → α)
    (f g : Fin r → Fin (M * P)) (hf : StrictMono f) (hg : StrictMono g)
    (hmatch : ∀ t, x (f t) = y (g t))
    (bad : ℕ × ℕ → Prop) (a₀ : ℕ)
    (hsep : BlockSegmentSeparation x y bad a₀)
    (b : ℕ × ℕ) (hb : bad b)
    (hvisit : ∃ t, ((f t).val / P, (g t).val / P) = b)
    (hlarge : a₀ ≤
      (Finset.univ.filter (fun t => ((f t).val / P, (g t).val / P) = b)).card) :
    (Finset.univ.filter (fun t => ((f t).val / P, (g t).val / P) = b)).card ≤
      100 * (((matchingSpan f (fun t => ((f t).val / P, (g t).val / P)) b).card -
        (Finset.univ.filter (fun t => ((f t).val / P, (g t).val / P) = b)).card) +
        ((matchingSpan g (fun t => ((f t).val / P, (g t).val / P)) b).card -
        (Finset.univ.filter (fun t => ((f t).val / P, (g t).val / P) = b)).card)) := by
  classical
  set lab : Fin r → ℕ × ℕ := fun t => ((f t).val / P, (g t).val / P) with hlab
  set S := Finset.univ.filter (fun t => lab t = b) with hS
  have hSne : S.Nonempty := by
    obtain ⟨t, ht⟩ := hvisit; exact ⟨t, by simp [hS, hlab, ht]⟩
  set t0 := S.min' hSne
  set t1 := S.max' hSne
  have ht0 : t0 ∈ S := S.min'_mem hSne
  have ht1 : t1 ∈ S := S.max'_mem hSne
  have hlabS : ∀ t ∈ S, (f t).val / P = b.1 ∧ (g t).val / P = b.2 := by
    intro t ht
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, hlab] at ht
    rw [← ht]; exact ⟨rfl, rfl⟩
  have hmin : ∀ t ∈ S, t0 ≤ t := fun t ht => S.min'_le t ht
  have hmax : ∀ t ∈ S, t ≤ t1 := fun t ht => S.le_max' t ht
  -- block bounds
  have blk : ∀ (n : ℕ) (c : ℕ), n / P = c → c * P ≤ n ∧ n < c * P + P := by
    intro n c h
    subst h
    constructor
    · exact Nat.div_mul_le_self n P
    · have := Nat.lt_div_mul_add (a := n) hP; linarith
  obtain ⟨f0l, f0h⟩ := blk _ _ (hlabS t0 ht0).1
  obtain ⟨f1l, f1h⟩ := blk _ _ (hlabS t1 ht1).1
  obtain ⟨g0l, g0h⟩ := blk _ _ (hlabS t0 ht0).2
  obtain ⟨g1l, g1h⟩ := blk _ _ (hlabS t1 ht1).2
  have hf01 : (f t0).val ≤ (f t1).val := hf.monotone (hmin t1 ht1)
  have hg01 : (g t0).val ≤ (g t1).val := hg.monotone (hmin t1 ht1)
  set Lf := (f t1).val + 1 - (f t0).val
  set Lg := (g t1).val + 1 - (g t0).val
  -- card S ≤ Lf, Lg
  have hcardIcc : ∀ (u : Fin r → Fin (M * P)), StrictMono u →
      S.card ≤ (u t1).val + 1 - (u t0).val := by
    intro u hu
    have : S.card ≤ (Finset.Icc (u t0) (u t1)).card := by
      apply Finset.card_le_card_of_injOn u
      · intro t ht
        exact Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨hu.monotone (hmin t ht), hu.monotone (hmax t ht)⟩)
      · exact hu.injective.injOn
    rwa [Fin.card_Icc] at this
  have hcf := hcardIcc f hf
  have hcg := hcardIcc g hg
  -- spans
  have hspan : ∀ (u : Fin r → Fin (M * P)), StrictMono u →
      (u t1).val + 1 - (u t0).val ≤ (matchingSpan u lab b).card := by
    intro u hu
    have : Finset.Icc (u t0) (u t1) ⊆ matchingSpan u lab b := by
      intro p hp
      rw [Finset.mem_Icc] at hp
      rw [mem_matchingSpan]
      have e0 : lab t0 = b := by simpa [hS] using ht0
      have e1 : lab t1 = b := by simpa [hS] using ht1
      exact ⟨t0, t1, e0, e1, hp.1, hp.2⟩
    have := Finset.card_le_card this
    rwa [Fin.card_Icc] at this
  have hsf := hspan f hf
  have hsg := hspan g hg
  set A := max Lf Lg with hA
  have hAP : A ≤ P := by
    rw [hA]; apply max_le
    · have : (f t1).val < b.1 * P + P := f1h; omega
    · have : (g t1).val < b.2 * P + P := g1h; omega
  obtain ⟨i, hi1, hi2, hi3, hi4⟩ := h49_window (b.1 * P) (f t0).val (f t1).val P A f0l hf01 f1h
    (le_max_left _ _) hAP
  obtain ⟨j, hj1, hj2, hj3, hj4⟩ := h49_window (b.2 * P) (g t0).val (g t1).val P A g0l hg01 g1h
    (le_max_right _ _) hAP
  have hb1 : b.1 < M := by
    have := (f t0).isLt
    by_contra hc; push_neg at hc
    have : M * P ≤ b.1 * P := Nat.mul_le_mul_right _ hc
    omega
  have hb2 : b.2 < M := by
    have := (g t0).isLt
    by_contra hc; push_neg at hc
    have : M * P ≤ b.2 * P := Nat.mul_le_mul_right _ hc
    omega
  obtain ⟨w, hwx, hwy, hwl⟩ := h49_ofFn_sub x y f g hf hg hmatch S i j A A
    (fun t ht => le_trans hi3 (hf.monotone (hmin t ht)))
    (fun t ht => lt_of_le_of_lt (hf.monotone (hmax t ht)) hi4)
    (fun t ht => le_trans hj3 (hg.monotone (hmin t ht)))
    (fun t ht => lt_of_le_of_lt (hg.monotone (hmax t ht)) hj4)
  have hA0 : a₀ ≤ A := le_trans hlarge (le_trans hcf (le_max_left _ _))
  have key := hsep b hb hb1 hb2 i j A hi1 (by rw [add_mul, one_mul]; exact hi2) hj1
    (by rw [add_mul, one_mul]; exact hj2) hA0 w hwx hwy
  rw [hwl] at key
  have : A ≤ Lf ∨ A ≤ Lg := by rw [hA]; omega
  omega

