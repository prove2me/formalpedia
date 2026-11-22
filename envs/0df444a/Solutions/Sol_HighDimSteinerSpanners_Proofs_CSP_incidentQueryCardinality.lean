-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.CSP.incidentQueryCardinality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:50:42.355247+00:00
-- url     : https://prove2.me/submissions/4f66d3be-bddc-4dd8-8864-05aea87b27a3

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_Calibration
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_WitnessMoments

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section
namespace HighDimSteinerSpanners.Proofs.CSP
theorem _root_.solution : ∀ {N : ℕ} (S : Finset (Fin N)),
    2 * ((S.card : ℤ) * ((N - 1 : ℕ) : ℤ) - ((candA1 S).card : ℤ)) ≤ (S.card : ℤ) ^ 2 := by
  intro N S
  let Ord : Finset (Fin N × Fin N) :=
    S.biUnion (fun u => ((Finset.univ : Finset (Fin N)).erase u).image (fun v => (u, v)))
  have hOrd_card : Ord.card = S.card * (N - 1) := by
    rw [Finset.card_biUnion]
    · have h_inner : ∀ u ∈ S,
          (((Finset.univ : Finset (Fin N)).erase u).image (fun v => (u, v))).card = N - 1 := by
        intro u _
        rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2),
          Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_fin]
      rw [Finset.sum_congr rfl h_inner, Finset.sum_const, smul_eq_mul]
    · intro u₁ _ u₂ _ hne
      simp only [Function.onFun, Finset.disjoint_left]
      intro p hp1 hp2
      rcases Finset.mem_image.mp hp1 with ⟨_, _, rfl⟩
      rcases Finset.mem_image.mp hp2 with ⟨_, _, hp⟩
      exact hne (Prod.mk.inj hp).1.symm
  let B_lt : Finset (Fin N × Fin N) := (S ×ˢ S).filter (fun uv => uv.1 < uv.2)
  let B_gt : Finset (Fin N × Fin N) := (S ×ˢ S).filter (fun uv => uv.2 < uv.1)
  let g : Fin N × Fin N → (Fin N × Fin N) ⊕ (Fin N × Fin N) :=
    fun ab =>
      if ab.1 < ab.2 then Sum.inl ab
      else if ab.2 ∈ S then Sum.inr (ab.2, ab.1)
      else Sum.inl (ab.2, ab.1)
  have hOrd_le : Ord.card ≤ (candA1 S).card + B_lt.card := by
    rw [← Finset.card_disjSum]
    apply Finset.card_le_card_of_injOn g
    · intro ab hab_mem
      simp only [Ord, Finset.mem_coe, Finset.mem_biUnion, Finset.mem_image,
        Finset.mem_erase, Finset.mem_univ, and_true] at hab_mem
      rcases hab_mem with ⟨a₀, ha₀, b₀, hba, rfl⟩
      dsimp [g]
      split_ifs with hlt hbS
      · simp only [Finset.mem_coe, Finset.mem_disjSum]
        refine Or.inl ⟨(a₀, b₀), ?_, rfl⟩
        simp only [candA1, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hlt, Or.inl ha₀⟩
      · simp only [Finset.mem_coe, Finset.mem_disjSum]
        refine Or.inr ⟨(b₀, a₀), ?_, rfl⟩
        simp only [B_lt, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hbS, ha₀⟩, lt_of_le_of_ne (not_lt.mp hlt) hba⟩
      · simp only [Finset.mem_coe, Finset.mem_disjSum]
        refine Or.inl ⟨(b₀, a₀), ?_, rfl⟩
        simp only [candA1, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨lt_of_le_of_ne (not_lt.mp hlt) hba, Or.inr ha₀⟩
    · intro ab₁ h₁ ab₂ h₂ heq
      simp only [Ord, Finset.mem_coe, Finset.mem_biUnion, Finset.mem_image,
        Finset.mem_erase, Finset.mem_univ, and_true] at h₁ h₂
      rcases h₁ with ⟨a₁, ha₁, b₁, _, rfl⟩
      rcases h₂ with ⟨a₂, ha₂, b₂, _, rfl⟩
      dsimp [g] at heq
      by_cases hlt₁ : a₁ < b₁ <;> by_cases hlt₂ : a₂ < b₂
      · rw [if_pos hlt₁, if_pos hlt₂] at heq
        exact Sum.inl.inj heq
      · rw [if_pos hlt₁, if_neg hlt₂] at heq
        by_cases hb₂ : b₂ ∈ S
        · rw [if_pos hb₂] at heq
          cases heq
        · rw [if_neg hb₂] at heq
          rcases Prod.mk.inj (Sum.inl.inj heq) with ⟨rfl, _⟩
          exact absurd ha₁ hb₂
      · rw [if_neg hlt₁, if_pos hlt₂] at heq
        by_cases hb₁ : b₁ ∈ S
        · rw [if_pos hb₁] at heq
          cases heq
        · rw [if_neg hb₁] at heq
          rcases Prod.mk.inj (Sum.inl.inj heq) with ⟨rfl, _⟩
          exact absurd ha₂ hb₁
      · rw [if_neg hlt₁, if_neg hlt₂] at heq
        by_cases hb₁ : b₁ ∈ S <;> by_cases hb₂ : b₂ ∈ S
        · rw [if_pos hb₁, if_pos hb₂] at heq
          rcases Prod.mk.inj (Sum.inr.inj heq) with ⟨rfl, rfl⟩
          rfl
        · rw [if_pos hb₁, if_neg hb₂] at heq
          cases heq
        · rw [if_neg hb₁, if_pos hb₂] at heq
          cases heq
        · rw [if_neg hb₁, if_neg hb₂] at heq
          rcases Prod.mk.inj (Sum.inl.inj heq) with ⟨rfl, rfl⟩
          rfl
  have hB_swap : B_lt.card ≤ B_gt.card := by
    apply Finset.card_le_card_of_injOn Prod.swap
    · intro uv huv
      simp only [B_lt, B_gt, Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Prod.swap]
          at huv ⊢
      exact ⟨⟨huv.1.2, huv.1.1⟩, huv.2⟩
    · intro uv₁ _ uv₂ _ heq
      exact Prod.swap_injective heq
  have hB_disj : Disjoint B_lt B_gt := by
    rw [Finset.disjoint_left]
    intro uv h₁ h₂
    simp only [B_lt, B_gt, Finset.mem_filter] at h₁ h₂
    exact lt_asymm h₁.2 h₂.2
  have hB_sub : B_lt ∪ B_gt ⊆ S ×ˢ S :=
    Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hB_two : 2 * B_lt.card ≤ S.card ^ 2 := by
    have hc := Finset.card_le_card hB_sub
    rw [Finset.card_union_of_disjoint hB_disj, Finset.card_product, ← sq] at hc
    omega
  have hnat : 2 * (S.card * (N - 1)) ≤ 2 * (candA1 S).card + S.card ^ 2 := by
    omega
  have hint : ((2 * (S.card * (N - 1)) : ℕ) : ℤ) ≤
      ((2 * (candA1 S).card + S.card ^ 2 : ℕ) : ℤ) := by
    exact_mod_cast hnat
  push_cast at hint
  linarith
end HighDimSteinerSpanners.Proofs.CSP
