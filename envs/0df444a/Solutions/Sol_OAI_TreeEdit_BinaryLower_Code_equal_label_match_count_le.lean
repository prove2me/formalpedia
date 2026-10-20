-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.Code.equal_label_match_count_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:29:35.522992+00:00
-- url     : https://prove2.me/submissions/a83906a7-a464-42fc-b268-3ecf6e11e39f

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

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.Code
theorem h49_lcs_succ {α : Type*} (x y : List α) (a b : ℕ) (ha : a < x.length) (hb : b < y.length)
    (h : x[a] = y[b]) : OAI.TreeEdit.lcs (x.take a) (y.take b) + 1 ≤ OAI.TreeEdit.lcs x y := by
  obtain ⟨z, hzx, hzy, hz⟩ := OAI.TreeEdit.exists_lcs (x.take a) (y.take b)
  have h1 : (z ++ [x[a]]).Sublist x := by
    have : (z ++ [x[a]]).Sublist (x.take (a+1)) := by
      rw [List.take_succ_eq_append_getElem ha]; exact hzx.append (List.Sublist.refl _)
    exact this.trans (List.take_sublist _ _)
  have h2 : (z ++ [x[a]]).Sublist y := by
    have : (z ++ [x[a]]).Sublist (y.take (b+1)) := by
      rw [List.take_succ_eq_append_getElem hb, h]; exact hzy.append (List.Sublist.refl _)
    exact this.trans (List.take_sublist _ _)
  have := OAI.TreeEdit.length_le_lcs h1 h2
  simp only [List.length_append, List.length_singleton] at this
  omega

theorem h49_fiber_card {P : ℕ} (hP : 0 < P) (S : Finset (ℕ × ℕ)) (φ : ℕ × ℕ → ℕ)
    (hinj : Set.InjOn φ S) (a : ℕ) (h : ∀ p ∈ S, φ p / P = a) : S.card ≤ P := by
  rw [← Finset.card_image_of_injOn hinj]
  have hsub : S.image φ ⊆ Finset.Ico (P*a) (P*a+P) := by
    intro v hv
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hv
    have h1 := Nat.div_add_mod (φ p) P
    have h2 := Nat.mod_lt (φ p) hP
    rw [h p hp] at h1
    rw [Finset.mem_Ico]; constructor <;> omega
  simpa using Finset.card_le_card hsub

theorem h49_chain_core {α : Type*} {P : ℕ} (hP : 0 < P) (n : ℕ) : ∀ (T : Finset (ℕ × ℕ)) (x y : List α),
    T.card = n →
    (∀ p ∈ T, ∀ q ∈ T, p.1 < q.1 ↔ p.2 < q.2) →
    (∀ p ∈ T, ∀ q ∈ T, p.1 = q.1 → p = q) →
    (∀ p ∈ T, ∃ h1 : p.1/P < x.length, ∃ h2 : p.2/P < y.length, x[p.1/P] = y[p.2/P]) →
    T.card ≤ P * OAI.TreeEdit.lcs x y := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro T x y hT hch hinj hl
  rcases T.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨q, hq, hqmax⟩ := T.exists_max_image Prod.fst hne
  have hq2 : ∀ p ∈ T, p.2 ≤ q.2 := by
    intro p hp; by_contra hc; push_neg at hc
    have := (hch q hq p hp).2 hc
    have := hqmax p hp; omega
  have hinj2 : ∀ p ∈ T, ∀ r ∈ T, p.2 = r.2 → p = r := by
    intro p hp r hr he
    apply hinj p hp r hr
    have h1 := hch p hp r hr
    have h2 := hch r hr p hp
    rcases lt_trichotomy p.1 r.1 with h | h | h
    · have := h1.1 h; omega
    · exact h
    · have := h2.1 h; omega
  obtain ⟨ha, hb, hab⟩ := hl q hq
  set a := q.1/P with ha_def
  set b := q.2/P with hb_def
  set T' := T.filter (fun p => p.1/P < a ∧ p.2/P < b) with hT'
  have hqT' : q ∉ T' := by simp [hT', ← ha_def]
  have hT'lt : T'.card < n := by
    rw [← hT]
    exact Finset.card_lt_card ⟨Finset.filter_subset _ _, fun h => hqT' (h hq)⟩
  have hsubT : ∀ p ∈ T', p ∈ T := fun p hp => (Finset.mem_filter.1 hp).1
  have ih' := ih T'.card hT'lt T' (x.take a) (y.take b) rfl
    (fun p hp r hr => hch p (hsubT p hp) r (hsubT r hr))
    (fun p hp r hr => hinj p (hsubT p hp) r (hsubT r hr))
    (by
      intro p hp
      have hp' := (Finset.mem_filter.1 hp).2
      obtain ⟨h1, h2, h3⟩ := hl p (hsubT p hp)
      have l1 : p.1/P < (x.take a).length := by rw [List.length_take]; omega
      have l2 : p.2/P < (y.take b).length := by rw [List.length_take]; omega
      refine ⟨l1, l2, ?_⟩
      rw [List.getElem_take, List.getElem_take]; exact h3)
  have hrest : (T.filter (fun p => ¬(p.1/P < a ∧ p.2/P < b))).card ≤ P := by
    have hle1 : ∀ p ∈ T, p.1/P ≤ a := fun p hp => Nat.div_le_div_right (hqmax p hp)
    have hle2 : ∀ p ∈ T, p.2/P ≤ b := fun p hp => Nat.div_le_div_right (hq2 p hp)
    by_cases hR : ∃ r ∈ T, r.1/P = a ∧ r.2/P < b
    · obtain ⟨r, hr, hr1, hr2⟩ := hR
      apply h49_fiber_card hP _ Prod.fst (fun p hp s hs h => hinj p (Finset.mem_filter.1 hp).1 s (Finset.mem_filter.1 hs).1 h) a
      intro p hp
      obtain ⟨hpT, hpn⟩ := Finset.mem_filter.1 hp
      by_contra hne
      have h1 : p.1/P < a := lt_of_le_of_ne (hle1 p hpT) hne
      have h2 : p.2/P = b := by have := hle2 p hpT; by_contra h'; exact hpn ⟨h1, by omega⟩
      have h3 : r.2 < p.2 := by
        by_contra h'; push_neg at h'
        have := Nat.div_le_div_right (c := P) h'; omega
      have h4 := (hch r hr p hpT).2 h3
      have := Nat.div_le_div_right (c := P) h4.le
      omega
    · push_neg at hR
      apply h49_fiber_card hP _ Prod.snd (fun p hp s hs h => hinj2 p (Finset.mem_filter.1 hp).1 s (Finset.mem_filter.1 hs).1 h) b
      intro p hp
      obtain ⟨hpT, hpn⟩ := Finset.mem_filter.1 hp
      by_contra hne
      have h2 : p.2/P < b := lt_of_le_of_ne (hle2 p hpT) hne
      have h1 : p.1/P = a := by have := hle1 p hpT; by_contra h'; exact hpn ⟨by omega, h2⟩
      have := hR p hpT h1; omega
  have hsplit := Finset.card_filter_add_card_filter_not (s := T) (fun p => p.1/P < a ∧ p.2/P < b)
  have hlcs := h49_lcs_succ x y a b ha hb hab
  calc T.card = T'.card + (T.filter (fun p => ¬(p.1/P < a ∧ p.2/P < b))).card := hsplit.symm
    _ ≤ P * OAI.TreeEdit.lcs (x.take a) (y.take b) + P := Nat.add_le_add ih' hrest
    _ = P * (OAI.TreeEdit.lcs (x.take a) (y.take b) + 1) := by ring
    _ ≤ P * OAI.TreeEdit.lcs x y := Nat.mul_le_mul_left _ hlcs

theorem h49_equal_label {α : Type*} {N P : ℕ} (hP : 0 < P)
    (x y : List α) (f g : Fin N → ℕ) (hf : StrictMono f) (hg : StrictMono g)
    (hfx : ∀ i, f i / P < x.length) (hgy : ∀ i, g i / P < y.length)
    (heq : ∀ i, x.get ⟨f i / P, hfx i⟩ = y.get ⟨g i / P, hgy i⟩) :
    N ≤ P * OAI.TreeEdit.lcs x y := by
  classical
  let T := Finset.univ.image (fun i => (f i, g i))
  have hTc : T.card = N := by
    rw [Finset.card_image_of_injective _ (fun i j h => hf.injective (congrArg Prod.fst h))]
    simp
  rw [← hTc]
  apply h49_chain_core hP T.card T x y rfl
  · intro p hp q hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hq
    exact hf.lt_iff_lt.trans hg.lt_iff_lt.symm
  · intro p hp q hq h
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hq
    have := hf.injective h; subst this; rfl
  · intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hp
    exact ⟨hfx i, hgy i, heq i⟩

theorem solution {α : Type*} {N P : ℕ} (hP : 0 < P)
    (x y : List α) (f g : Fin N → ℕ) (hf : StrictMono f) (hg : StrictMono g)
    (hfx : ∀ i, f i / P < x.length) (hgy : ∀ i, g i / P < y.length)
    (heq : ∀ i, x.get ⟨f i / P, hfx i⟩ = y.get ⟨g i / P, hgy i⟩) :
    N ≤ P * lcs x y := by
  exact h49_equal_label hP x y f g hf hg hfx hgy heq

