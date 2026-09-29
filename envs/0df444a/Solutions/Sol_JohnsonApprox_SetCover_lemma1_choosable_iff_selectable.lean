-- Prove2me | solution 1 for JohnsonApprox.SetCover.lemma1_choosable_iff_selectable
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T18:46:40.940009+00:00
-- url     : https://prove2.me/submissions/5982f12b-e1e1-4dfd-ae65-4710e09ea367

import Mathlib
import Definitions.Def_JohnsonApprox_SetCover_Problem
import Definitions.Def_JohnsonApprox_SetCover_C1
import Definitions.Def_JohnsonApprox_SetCover_Config



namespace JohnsonApprox.SetCover

open Finset

lemma harmonic_sub_ge (a b : ℕ) (hba : b ≤ a) (ha : 0 < a) :
    ((a : ℚ) - b) / a ≤ harmonic a - harmonic b := by
  unfold harmonic
  rw [← Finset.sum_range_add_sum_Ico _ hba, add_sub_cancel_left]
  have : ∑ _i ∈ Ico b a, (1 / (a : ℚ)) ≤ ∑ i ∈ Ico b a, ((↑(i + 1) : ℚ))⁻¹ := by
    apply sum_le_sum
    intro i hi
    rw [mem_Ico] at hi
    rw [one_div]
    apply inv_anti₀ (by positivity)
    exact_mod_cast (by omega : i + 1 ≤ a)
  rw [sum_const, Nat.card_Ico, nsmul_eq_mul] at this
  rw [Nat.cast_sub hba] at this
  calc ((a : ℚ) - b) / a = ((a : ℚ) - b) * (1 / a) := by ring
    _ ≤ _ := this

lemma harmonic_nonneg' (n : ℕ) : 0 ≤ harmonic n := by
  unfold harmonic; exact sum_nonneg (fun i _ => by positivity)

lemma harmonic_mono' {a b : ℕ} (h : a ≤ b) : harmonic a ≤ harmonic b := by
  unfold harmonic
  exact sum_le_sum_of_subset_of_nonneg (range_mono h) (fun i _ _ => by positivity)

variable {ι α : Type} [Fintype ι] [DecidableEq α]

lemma run_of_reach' [DecidableEq ι] (S : ι → Finset α) {σ σf : State ι α}
    (hr : Relation.ReflTransGen (Step S) σ σf) (hf : Halts σf) :
    ∀ h : Finset.univ.biUnion σ.SET = σ.UNCOV, ∃ js : List ι,
      IsRun (⟨σ.UNCOV, σ.SET, h⟩ : Config ι α) js ∧ σf.SUB = σ.SUB ∪ js.toFinset.image S := by
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro h
    exact ⟨[], IsRun.halt _ hf, by simp⟩
  | @head σ σ' hst _ ih =>
    intro h
    obtain ⟨j, hnh, hmax, rfl⟩ := hst
    have h' : Finset.univ.biUnion (fun i => σ.SET i \ σ.SET j) = σ.UNCOV \ σ.SET j := by
      rw [← h]; ext x; simp only [mem_biUnion, mem_univ, true_and, mem_sdiff]
      constructor
      · rintro ⟨i, hx, hxj⟩; exact ⟨⟨i, hx⟩, hxj⟩
      · rintro ⟨⟨i, hx⟩, hxj⟩; exact ⟨i, hx, hxj⟩
    obtain ⟨js, hrun, hsub⟩ := ih h'
    refine ⟨j :: js, IsRun.step _ j _ js ⟨hnh, hmax, rfl, rfl⟩ hrun, ?_⟩
    rw [hsub]; ext x
    simp only [mem_union, mem_insert, mem_image, List.mem_toFinset, List.mem_cons]
    constructor
    · rintro ((h1 | h1) | ⟨a, ha, hax⟩)
      · exact Or.inr ⟨j, Or.inl rfl, h1.symm⟩
      · exact Or.inl h1
      · exact Or.inr ⟨a, Or.inr ha, hax⟩
    · rintro (h1 | ⟨a, (rfl | ha), hax⟩)
      · exact Or.inl (Or.inr h1)
      · exact Or.inl (Or.inl hax.symm)
      · exact Or.inr ⟨a, ha, hax⟩

lemma reach_of_run [DecidableEq ι] (S : ι → Finset α) {K : Config ι α} {js : List ι}
    (hr : IsRun K js) : ∀ SUB0 : Finset (Finset α), ∃ σf : State ι α,
      Relation.ReflTransGen (Step S) ⟨SUB0, K.UNCOV, K.SET⟩ σf ∧ Halts σf ∧
        σf.SUB = SUB0 ∪ js.toFinset.image S := by
  induction hr with
  | halt K hK =>
    intro SUB0; exact ⟨_, Relation.ReflTransGen.refl, hK, by simp⟩
  | step K j K' js hstep _ ih =>
    intro SUB0
    obtain ⟨hne, hmax, hU, hS⟩ := hstep
    obtain ⟨σf, hr, hh, hsub⟩ := ih (insert (S j) SUB0)
    refine ⟨σf, Relation.ReflTransGen.head ⟨j, hne, hmax, ?_⟩ hr, hh, ?_⟩
    · rw [hU, hS]
    · rw [hsub]; ext x
      simp only [mem_union, mem_insert, mem_image, List.mem_toFinset, List.mem_cons]
      constructor
      · rintro ((h1 | h1) | ⟨a, ha, hax⟩)
        · exact Or.inr ⟨j, Or.inl rfl, h1.symm⟩
        · exact Or.inl h1
        · exact Or.inr ⟨a, Or.inr ha, hax⟩
      · rintro (h1 | ⟨a, (rfl | ha), hax⟩)
        · exact Or.inl (Or.inr h1)
        · exact Or.inl (Or.inl hax.symm)
        · exact Or.inr ⟨a, ha, hax⟩

theorem lemma1_core [DecidableEq ι]
    (S : ι → Finset α) (hS : Function.Injective S)
    (F₁ : Finset (Finset α)) (hF₁ : F₁ ∈ subcovers S) :
    Choosable S F₁ ↔ Selectable (initConfig S) (Finset.univ.filter (fun i => S i ∈ F₁)) := by
  constructor
  · rintro ⟨σ, hr, hh, rfl⟩
    obtain ⟨js, hrun, hsub⟩ := run_of_reach' S hr hh rfl
    refine ⟨js, hrun, ?_⟩
    simp only [init, empty_union] at hsub
    rw [hsub]; ext i
    simp only [mem_filter, mem_univ, true_and, mem_image, List.mem_toFinset]
    constructor
    · rintro ⟨a, ha, hai⟩; rw [← hS hai]; exact ha
    · intro hi; exact ⟨i, hi, rfl⟩
  · rintro ⟨js, hrun, hjs⟩
    obtain ⟨σf, hr, hh, hsub⟩ := reach_of_run S hrun ∅
    refine ⟨σf, hr, hh, ?_⟩
    rw [hsub, empty_union, ← hjs]
    unfold subcovers at hF₁; rw [mem_filter, mem_powerset] at hF₁
    ext A; simp only [mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hi
    · intro hA
      have := hF₁.1 hA; unfold family at this
      obtain ⟨i, _, rfl⟩ := mem_image.1 this
      exact ⟨i, hA, rfl⟩

end JohnsonApprox.SetCover

open JohnsonApprox.SetCover

theorem solution {ι α : Type} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (S : ι → Finset α) (hS : Function.Injective S)
    (F₁ : Finset (Finset α)) (hF₁ : F₁ ∈ subcovers S) :
    Choosable S F₁ ↔ Selectable (initConfig S) (Finset.univ.filter (fun i => S i ∈ F₁)) := by
  exact lemma1_core S hS F₁ hF₁
