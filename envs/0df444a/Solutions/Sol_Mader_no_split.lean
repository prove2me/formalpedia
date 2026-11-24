-- Prove2me | solution 1 for Mader.no_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:54:24.586286+00:00
-- url     : https://prove2.me/submissions/84a428c5-47f6-463a-aaac-94d910f14431

module
public import Mathlib
public import Definitions.Def_MaderLib_MaderAux
public import Definitions.Def_MaderLib_MaderSteps
public import Theorems.Thm_Mader_side_card
public import Theorems.Thm_Mader_dbl_union_le


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open Mader
variable {V : Type*} (G : SimpleGraph V)
namespace Mader
theorem _root_.solution [DecidableEq V] {S X U₁ U₂ : Finset V} {m n k : ℕ} (hm : 4 * k * n ≤ m)
    (hmin : ∀ S' : Finset V, S'.card < S.card → 2 * k ≤ S'.card →
       (dbl G S' : ℤ) * n ≤ (m : ℤ) * ((S'.card : ℤ) - k))
    (hP : (m : ℤ) * ((S.card : ℤ) - k) < (dbl G S : ℤ) * n)
    (hdeg : ∀ v ∈ S, m < 2 * ndeg G S v * n)
    (hX : X.card ≤ k) (hS : S = U₁ ∪ U₂ ∪ X) (h12 : Disjoint U₁ U₂) (h1X : Disjoint U₁ X)
    (h2X : Disjoint U₂ X) (hne1 : U₁.Nonempty) (hne2 : U₂.Nonempty)
    (hno : ∀ a ∈ U₁, ∀ b ∈ U₂, ¬ G.Adj a b) : False := by
  classical
  have hcS : S.card = U₁.card + U₂.card + X.card := by
    rw [hS, card_union_of_disjoint (disjoint_union_left.2 ⟨h1X, h2X⟩),
      card_union_of_disjoint h12]
  have hc1 : (U₁ ∪ X).card = U₁.card + X.card := card_union_of_disjoint h1X
  have hc2 : (U₂ ∪ X).card = U₂.card + X.card := card_union_of_disjoint h2X
  have hp1 : 0 < U₂.card := hne2.card_pos
  have hp2 : 0 < U₁.card := hne1.card_pos
  obtain ⟨x, hx⟩ := hne1
  obtain ⟨y, hy⟩ := hne2
  have hxS : x ∈ S := by rw [hS]; simp [hx]
  have hyS : y ∈ S := by rw [hS]; simp [hy]
  have hb1 : 2 * k < (U₁ ∪ X).card := side_card G hm hdeg hxS (by
    intro w hw hadj
    rw [hS] at hw
    simp only [mem_union] at hw ⊢
    rcases hw with (hw | hw) | hw
    · exact Or.inl hw
    · exact absurd hadj (hno x hx w hw)
    · exact Or.inr hw)
  have hb2 : 2 * k < (U₂ ∪ X).card := side_card G hm hdeg hyS (by
    intro w hw hadj
    rw [hS] at hw
    simp only [mem_union] at hw ⊢
    rcases hw with (hw | hw) | hw
    · exact absurd hadj.symm (hno w hw y hy)
    · exact Or.inl hw
    · exact Or.inr hw)
  have e1 := hmin (U₁ ∪ X) (by omega) (by omega)
  have e2 := hmin (U₂ ∪ X) (by omega) (by omega)
  have hcov := dbl_union_le G (S := S) (H₁ := U₁ ∪ X) (H₂ := U₂ ∪ X) (by
    intro a ha b hb hadj
    rw [hS] at ha hb
    simp only [mem_union] at ha hb ⊢
    rcases ha with (ha | ha) | ha <;> rcases hb with (hb | hb) | hb
    all_goals first
      | exact absurd hadj (hno a ha b hb)
      | exact absurd hadj.symm (hno b hb a ha)
      | tauto)
  rw [hc1] at e1
  rw [hc2] at e2
  have hcz : (S.card : ℤ) = U₁.card + U₂.card + X.card := by exact_mod_cast hcS
  have hXz : (X.card : ℤ) ≤ k := by exact_mod_cast hX
  have hcovz : (dbl G S : ℤ) * n ≤ ((dbl G (U₁ ∪ X) : ℤ) + dbl G (U₂ ∪ X)) * n := by
    apply mul_le_mul_of_nonneg_right (by exact_mod_cast hcov) (by positivity)
  push_cast at e1 e2
  nlinarith [mul_le_mul_of_nonneg_left hXz (show (0 : ℤ) ≤ m by positivity)]
end Mader
