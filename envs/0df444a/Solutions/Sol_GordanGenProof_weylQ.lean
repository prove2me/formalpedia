-- Prove2me | solution 1 for GordanGenProof.weylQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:43:14.272084+00:00
-- url     : https://prove2.me/submissions/cb0b45fb-fc86-4413-88c4-98eda82ee59b

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_GordanCones
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GordanIntegerMultiple_ExistsIntMultiple
import Theorems.Thm_GordanGenProof_gcone_sub
import Theorems.Thm_GordanGenProof_mem_gcone
import Theorems.Thm_GordanGenProof_minkowskiQ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
namespace GordanGenProof
open Finset
private theorem rat_dotProduct_zero_right {n : ℕ} (a : Fin n → ℚ) : a ⬝ᵥ (0 : Fin n → ℚ) = 0 := by
  show ∑ j, a j * (0 : Fin n → ℚ) j = 0
  simp
private theorem rat_dotProduct_zero_left {n : ℕ} (x : Fin n → ℚ) : (0 : Fin n → ℚ) ⬝ᵥ x = 0 := by
  show ∑ j, (0 : Fin n → ℚ) j * x j = 0
  simp
private theorem rat_dotProduct_comm {n : ℕ} (a b : Fin n → ℚ) : a ⬝ᵥ b = b ⬝ᵥ a := by
  show ∑ j, a j * b j = ∑ j, b j * a j
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _
private theorem rat_dotProduct_add_left {n : ℕ} (a b x : Fin n → ℚ) : (a + b) ⬝ᵥ x = a ⬝ᵥ x + b ⬝ᵥ x := by
  show ∑ j, (a + b) j * x j = ∑ j, a j * x j + ∑ j, b j * x j
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => add_mul (a j) (b j) (x j)
private theorem rat_dotProduct_add_right {n : ℕ} (a x y : Fin n → ℚ) : a ⬝ᵥ (x + y) = a ⬝ᵥ x + a ⬝ᵥ y := by
  show ∑ j, a j * (x + y) j = ∑ j, a j * x j + ∑ j, a j * y j
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => mul_add (a j) (x j) (y j)
private theorem rat_dotProduct_smul_left {n : ℕ} (r : ℚ) (a x : Fin n → ℚ) : (r • a) ⬝ᵥ x = r * (a ⬝ᵥ x) := by
  show ∑ j, (r • a) j * x j = r * ∑ j, a j * x j
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => mul_assoc r (a j) (x j)
private theorem rat_dotProduct_smul_right {n : ℕ} (r : ℚ) (a x : Fin n → ℚ) : a ⬝ᵥ (r • x) = r * (a ⬝ᵥ x) := by
  show ∑ j, a j * (r • x) j = r * ∑ j, a j * x j
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => mul_left_comm (a j) r (x j)
private theorem dotProduct_nonneg_of_mem_hcone_of_mem_gcone {n : ℕ} {A : Finset (Fin n → ℚ)} {x d : Fin n → ℚ}
    (hx : x ∈ hcone A id) (hd : d ∈ gcone A id) : 0 ≤ d ⬝ᵥ x := by
  have hsub : gcone A id ⊆ {e | 0 ≤ e ⬝ᵥ x} :=
    gcone_sub A id _
      (by show 0 ≤ (0 : Fin n → ℚ) ⬝ᵥ x; exact le_of_eq (rat_dotProduct_zero_left x).symm)
      (fun a ha b hb => by
        have ha' : 0 ≤ a ⬝ᵥ x := ha
        have hb' : 0 ≤ b ⬝ᵥ x := hb
        show 0 ≤ (a + b) ⬝ᵥ x
        rw [rat_dotProduct_add_left]
        exact add_nonneg ha' hb')
      (fun r hr a ha => by
        have ha' : 0 ≤ a ⬝ᵥ x := ha
        show 0 ≤ (r • a) ⬝ᵥ x
        rw [rat_dotProduct_smul_left]
        exact mul_nonneg hr ha')
      (fun a ha => hx a ha)
  exact hsub hd
end GordanGenProof
end

set_option autoImplicit false
set_option autoImplicit false
open GordanGenProof
open Finset
namespace GordanGenProof
theorem _root_.solution {n : ℕ} (A : Finset (Fin n → ℚ)) :
    ∃ B : Finset (Fin n → ℚ), hcone A id = gcone B id := by
  obtain ⟨B, hB⟩ := minkowskiQ A
  obtain ⟨D, hD⟩ := minkowskiQ B
  refine ⟨B, Set.Subset.antisymm ?_ ?_⟩
  · intro x hx
    rw [hD]
    show ∀ d ∈ D, 0 ≤ id d ⬝ᵥ x
    intro d hd
    have hdA : d ∈ gcone A id := by
      rw [hB]
      show ∀ b ∈ B, 0 ≤ id b ⬝ᵥ d
      intro b hb
      have hb' : id b ∈ gcone B id := mem_gcone hb
      rw [hD] at hb'
      have h2 : 0 ≤ id d ⬝ᵥ id b := hb' d hd
      show 0 ≤ b ⬝ᵥ d
      rw [rat_dotProduct_comm]
      exact h2
    exact dotProduct_nonneg_of_mem_hcone_of_mem_gcone hx hdA
  · refine gcone_sub B id _ ?_ ?_ ?_ ?_
    · show ∀ a ∈ A, 0 ≤ id a ⬝ᵥ (0 : Fin n → ℚ)
      intro a _
      exact le_of_eq (rat_dotProduct_zero_right _).symm
    · intro x hx y hy
      have hx' : ∀ a ∈ A, 0 ≤ id a ⬝ᵥ x := hx
      have hy' : ∀ a ∈ A, 0 ≤ id a ⬝ᵥ y := hy
      show ∀ a ∈ A, 0 ≤ id a ⬝ᵥ (x + y)
      intro a ha
      rw [rat_dotProduct_add_right]
      exact add_nonneg (hx' a ha) (hy' a ha)
    · intro r hr x hx
      have hx' : ∀ a ∈ A, 0 ≤ id a ⬝ᵥ x := hx
      show ∀ a ∈ A, 0 ≤ id a ⬝ᵥ (r • x)
      intro a ha
      rw [rat_dotProduct_smul_right]
      exact mul_nonneg hr (hx' a ha)
    · intro b hb
      show ∀ a ∈ A, 0 ≤ id a ⬝ᵥ id b
      intro a ha
      have h1 : id a ∈ gcone A id := mem_gcone ha
      rw [hB] at h1
      have h2 : 0 ≤ id b ⬝ᵥ id a := h1 b hb
      rw [rat_dotProduct_comm]
      exact h2
end GordanGenProof
