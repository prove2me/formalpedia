-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentCorrelation.fullCorrelation_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:09:22.444378+00:00
-- url     : https://prove2.me/submissions/179b3a8d-9a57-45aa-b11f-638eb5d9bf30

import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_Correlation
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Group.Pi.Units
import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_CRT

set_option autoImplicit false
open OAI
open scoped BigOperators Classical
open OAI.SevenEighths OAI.SevenEighths.CenteredMomentCorrelation
noncomputable section
variable {A B : Type*} [CommRing A] [CommRing B] [Fintype A] [Fintype B]
namespace OAI.SevenEighths.CenteredMomentCorrelation
theorem _root_.solution (u v k : A × B) (f₁ g₁ : A → ℂ) (f₂ g₂ : B → ℂ) :
    fullCorrelation (fun x => v * x) (fun y => u * y)
        (fun x => f₁ x.1 * f₂ x.2) (fun y => g₁ y.1 * g₂ y.2) k =
      fullCorrelation (fun x => v.1 * x) (fun y => u.1 * y) f₁ g₁ k.1 *
        fullCorrelation (fun x => v.2 * x) (fun y => u.2 * y) f₂ g₂ k.2 := by
  classical
  simp only [fullCorrelation, Fintype.sum_prod_type]
  have hterm (x₁ y₁ : A) (x₂ y₂ : B) :
      (if v * (x₁, x₂) - u * (y₁, y₂) = k
       then (f₁ x₁ * f₂ x₂) * star (g₁ y₁ * g₂ y₂) else 0) =
      (if v.1 * x₁ - u.1 * y₁ = k.1 then f₁ x₁ * star (g₁ y₁) else 0) *
      (if v.2 * x₂ - u.2 * y₂ = k.2 then f₂ x₂ * star (g₂ y₂) else 0) := by
    have heq : v * (x₁, x₂) - u * (y₁, y₂) = k ↔
        v.1 * x₁ - u.1 * y₁ = k.1 ∧ v.2 * x₂ - u.2 * y₂ = k.2 := by
      exact Prod.ext_iff
    by_cases h₁ : v.1 * x₁ - u.1 * y₁ = k.1 <;>
      by_cases h₂ : v.2 * x₂ - u.2 * y₂ = k.2 <;>
      simp [heq, h₁, h₂, star_mul] ; ring
  simp_rw [hterm]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x₁ _
  rw [Finset.sum_comm, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y₁ _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x₂ _
  rw [Finset.mul_sum]
end OAI.SevenEighths.CenteredMomentCorrelation
