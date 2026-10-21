-- Prove2me | solution 1 for ImprovedMMS.Additive.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T17:00:36.076262+00:00
-- url     : https://prove2.me/submissions/ef2fb8a1-8cb5-4f7e-ae19-e880e0cff8d0

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_ImprovedMMS_Additive_Instance

set_option autoImplicit false
open LittleCharity.MMS ImprovedMMS.Additive

open Classical

theorem ims_mono {n m : ℕ} {v : Fin n → Finset (Fin m) → ℝ} (hv : IsAdditive v) (i : Fin n)
    {S T : Finset (Fin m)} (h : S ⊆ T) : v i S ≤ v i T := by
  rw [hv.1 i S, hv.1 i T]
  exact Finset.sum_le_sum_of_subset_of_nonneg h (fun g _ _ => hv.2 i {g})

theorem ims_union {n m : ℕ} {v : Fin n → Finset (Fin m) → ℝ} (hv : IsAdditive v) (i : Fin n)
    {S T : Finset (Fin m)} (h : Disjoint S T) : v i (S ∪ T) = v i S + v i T := by
  rw [hv.1 i (S ∪ T), hv.1 i S, hv.1 i T]
  exact Finset.sum_union h

theorem ims_sdiff_ge {n m : ℕ} {v : Fin n → Finset (Fin m) → ℝ} (hv : IsAdditive v) (i : Fin n)
    (X Y : Finset (Fin m)) : v i X - v i Y ≤ v i (X \ Y) := by
  have h1 : v i X = v i (X \ Y) + v i (X ∩ Y) := by
    rw [← ims_union hv i (Finset.disjoint_sdiff_inter X Y), Finset.sdiff_union_inter]
  have h2 : v i (X ∩ Y) ≤ v i Y := ims_mono hv i Finset.inter_subset_right
  linarith

theorem ims_le_mms {m : ℕ} (w : Finset (Fin m) → ℝ) {k : ℕ} (hk : 0 < k) (S : Finset (Fin m))
    (c : ℝ) (f : Fin m → Fin k) (h : ∀ j, c ≤ w (S.filter (fun g => f g = j))) :
    c ≤ mms w k S := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  unfold mms
  exact le_ciSup_of_le (Finite.bddAbove_range _) f (le_ciInf h)

theorem ims_exists_part {m : ℕ} (w : Finset (Fin m) → ℝ) {k : ℕ} (hk : 0 < k) (S : Finset (Fin m))
    (c : ℝ) (h : c ≤ mms w k S) :
    ∃ f : Fin m → Fin k, ∀ j, c ≤ w (S.filter (fun g => f g = j)) := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have : Nonempty (Fin m → Fin k) := ⟨fun _ => ⟨0, hk⟩⟩
  obtain ⟨f, hf⟩ := exists_eq_ciSup_of_finite
    (f := fun f : Fin m → Fin k => ⨅ j, w (S.filter (fun g => f g = j)))
  refine ⟨f, fun j => ?_⟩
  have h' : c ≤ ⨅ j, w (S.filter (fun g => f g = j)) := by
    unfold mms at h
    rw [← hf] at h
    exact h
  exact h'.trans (ciInf_le (Finite.bddBelow_range _) j)

theorem ims_merge {n m : ℕ} {v : Fin n → Finset (Fin m) → ℝ} (i : Fin n) {k : ℕ} (hk : 2 ≤ k)
    (M D : Finset (Fin m)) (f : Fin m → Fin k) (c : ℝ)
    (hf : ∀ j, c ≤ v i (M.filter (fun x => f x = j))) (a b : Fin k) (hab : a ≠ b)
    (hD : ∀ x ∈ D, f x = a ∨ f x = b)
    (hmerge : c ≤ v i ((M.filter (fun x => f x = a ∨ f x = b)) \ D)) :
    c ≤ mms (v i) (k - 1) (M \ D) := by
  have hcard : Fintype.card {x : Fin k // x ≠ b} = k - 1 := by
    simp [Fintype.card_subtype_compl]
  let e : {x : Fin k // x ≠ b} ≃ Fin (k - 1) := Fintype.equivFinOfCardEq hcard
  let f₁ : Fin m → {x : Fin k // x ≠ b} := fun x => if h : f x = b then ⟨a, hab⟩ else ⟨f x, h⟩
  apply ims_le_mms (v i) (by omega) (M \ D) c (fun x => e (f₁ x))
  intro j
  obtain ⟨t, rfl⟩ := e.surjective j
  have key : ∀ x, e (f₁ x) = e t ↔ f₁ x = t := fun x => e.apply_eq_iff_eq
  by_cases hta : t.1 = a
  · have : (M \ D).filter (fun x => e (f₁ x) = e t) = (M.filter (fun x => f x = a ∨ f x = b)) \ D := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_sdiff, key]
      constructor
      · rintro ⟨⟨hxM, hxD⟩, h⟩
        refine ⟨⟨hxM, ?_⟩, hxD⟩
        by_cases hfb : f x = b
        · exact Or.inr hfb
        · left
          have := congrArg Subtype.val h
          simp [f₁, hfb] at this
          rw [this, hta]
      · rintro ⟨⟨hxM, hx⟩, hxD⟩
        refine ⟨⟨hxM, hxD⟩, ?_⟩
        apply Subtype.ext
        by_cases hfb : f x = b
        · simp [f₁, hfb, hta]
        · have : f x = a := hx.resolve_right hfb
          simp [f₁, hfb, hta, this, hab]
    rw [this]; exact hmerge
  · have : (M \ D).filter (fun x => e (f₁ x) = e t) = M.filter (fun x => f x = t.1) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_sdiff, key]
      constructor
      · rintro ⟨⟨hxM, _⟩, h⟩
        refine ⟨hxM, ?_⟩
        by_cases hfb : f x = b
        · have := congrArg Subtype.val h
          simp [f₁, hfb] at this
          exact absurd this.symm hta
        · have := congrArg Subtype.val h
          simpa [f₁, hfb] using this
      · rintro ⟨hxM, hx⟩
        have hfb : f x ≠ b := by rw [hx]; exact t.2
        refine ⟨⟨hxM, fun hxD => ?_⟩, Subtype.ext (by simp [f₁, hfb, hx, t.2])⟩
        rcases hD x hxD with h | h
        · exact hta (hx ▸ h)
        · exact hfb h
    rw [this]; exact hf t.1

theorem ims_remove_pair {n m : ℕ} {v : Fin n → Finset (Fin m) → ℝ} (hv : IsAdditive v) (i : Fin n)
    {k : ℕ} (hk : 2 ≤ k) (M : Finset (Fin m)) (hmms : 1 ≤ mms (v i) k M)
    (bj bk : Fin m) (hle : v i {bj, bk} ≤ 1) :
    1 ≤ mms (v i) (k - 1) (M \ {bj, bk}) := by
  obtain ⟨f, hf⟩ := ims_exists_part (v i) (by omega) M 1 hmms
  have hcardk : 1 < Fintype.card (Fin k) := by simp; omega
  obtain ⟨b, hb, hb'⟩ : ∃ b : Fin k, b ≠ f bj ∧ (f bk = f bj ∨ f bk = b) := by
    by_cases h : f bk = f bj
    · obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card hcardk (f bj)
      exact ⟨b, hb, Or.inl h⟩
    · exact ⟨f bk, fun h' => h h', Or.inr rfl⟩
  have hab : f bj ≠ b := fun h => hb h.symm
  refine ims_merge i hk M {bj, bk} f 1 hf (f bj) b hab ?_ ?_
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact hb'
  · have hU : (M.filter (fun x => f x = f bj ∨ f x = b)) =
        M.filter (fun x => f x = f bj) ∪ M.filter (fun x => f x = b) := by
      ext x; simp [Finset.mem_filter]; tauto
    have hdisj : Disjoint (M.filter (fun x => f x = f bj)) (M.filter (fun x => f x = b)) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_filter] at hx1 hx2
      exact hab (hx1.2.symm.trans hx2.2)
    have h2 := ims_sdiff_ge hv i (M.filter (fun x => f x = f bj ∨ f x = b)) {bj, bk}
    have hUv : v i (M.filter (fun x => f x = f bj ∨ f x = b)) =
        v i (M.filter (fun x => f x = f bj)) + v i (M.filter (fun x => f x = b)) := by
      rw [hU, ims_union hv i hdisj]
    have := hf (f bj); have := hf b
    linarith

theorem ims_remove_single {n m : ℕ} {v : Fin n → Finset (Fin m) → ℝ} (hv : IsAdditive v) (i : Fin n)
    {k : ℕ} (hk : 2 ≤ k) (M : Finset (Fin m)) (hmms : 1 ≤ mms (v i) k M)
    (bj : Fin m) :
    1 ≤ mms (v i) (k - 1) (M \ {bj}) := by
  obtain ⟨f, hf⟩ := ims_exists_part (v i) (by omega) M 1 hmms
  have hcardk : 1 < Fintype.card (Fin k) := by simp; omega
  obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card hcardk (f bj)
  have hab : f bj ≠ b := fun h => hb h.symm
  refine ims_merge i hk M {bj} f 1 hf (f bj) b hab ?_ ?_
  · intro x hx
    simp only [Finset.mem_singleton] at hx
    subst hx
    exact Or.inl rfl
  · refine le_trans (hf b) (ims_mono hv i ?_)
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton] at hx ⊢
    refine ⟨⟨hx.1, Or.inr hx.2⟩, ?_⟩
    rintro rfl
    exact hab hx.2

theorem ims_l32 {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (hv : IsAdditive v)
    (N : Finset (Fin n)) (M : Finset (Fin m)) (hN1 : ∀ i ∈ N, mms (v i) N.card M = 1)
    (hirr : IsIrreducible (3 / 4) v N M)
    (i : Fin n) (hi : i ∈ N) (bj bk : Fin m) (hbj : bj ∈ M) (hbk : bk ∈ M)
    (h : (3 / 4 : ℝ) ≤ v i {bj, bk}) :
    ∃ i' ∈ N, i' ≠ i ∧ 1 < v i' {bj, bk} := by
  by_contra hcon
  push_neg at hcon
  apply hirr
  refine ⟨{i}, by simpa using hi, Finset.singleton_nonempty _, {bj, bk}, ?_, fun _ => i, by simp, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  · intro i' hi'
    rw [Finset.mem_singleton] at hi'
    subst hi'
    have : ({bj, bk} : Finset (Fin m)).filter (fun _ => i' = i') = {bj, bk} := by simp
    rw [this, hN1 _ hi]
    linarith
  · intro k hk
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hk
    have h2 : 2 ≤ N.card := by
      have := Finset.one_lt_card.mpr ⟨i, hi, k, hk.1, fun h => hk.2 h.symm⟩
      omega
    have := ims_remove_pair hv k h2 M (by rw [hN1 k hk.1]) bj bk (hcon k hk.1 hk.2)
    rw [hN1 k hk.1]
    simpa using this

theorem solution {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (hv : IsAdditive v)
    (N : Finset (Fin n)) (M : Finset (Fin m)) (hN1 : ∀ i ∈ N, mms (v i) N.card M = 1)
    (hirr : IsIrreducible (3 / 4) v N M)
    (i : Fin n) (hi : i ∈ N) (bj bk : Fin m) (hbj : bj ∈ M) (hbk : bk ∈ M)
    (h : (3 / 4 : ℝ) ≤ v i {bj, bk}) :
    ∃ i' ∈ N, i' ≠ i ∧ 1 < v i' {bj, bk} :=
  ims_l32 v hv N M hN1 hirr i hi bj bk hbj hbk h
