-- Prove2me | solution 1 for OAI.PoissonFirstLocal.first_prime_product_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:36:42.646172+00:00
-- url     : https://prove2.me/submissions/373d5ce6-9e6e-4387-8a26-3654297ab4c4

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Theorems.Thm_OAI_PoissonChildCRT_mask_mul
import Theorems.Thm_OAI_PoissonFirstLocal_first_local_identity
section
namespace OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
namespace ShortDraftFiniteGaussFourier
open scoped Classical
open AddChar MulChar
variable {F : Type*} [Field F] [Fintype F]
end ShortDraftFiniteGaussFourier
namespace PoissonChildCRT
open scoped Classical
variable (n : ℕ) (χ : MulChar (ZMod n) ℂ)
end PoissonChildCRT
namespace PoissonFirstLocal
open scoped Classical
private theorem mask_mul (n a b : ℕ) :
    mask n (a * b) = mask n a * mask n b := by
  classical
  simp only [mask]
  by_cases hab : n.Coprime (a * b)
  · have ha : n.Coprime a := (Nat.coprime_mul_iff_right.mp hab).1
    have hb : n.Coprime b := (Nat.coprime_mul_iff_right.mp hab).2
    rw [if_pos hab, if_pos ha, if_pos hb]
    norm_num
  · have hna_or_hnb : ¬ n.Coprime a ∨ ¬ n.Coprime b := by
      by_contra h
      exact hab (Nat.coprime_mul_iff_right.mpr ⟨not_not.mp (not_or.mp h).1,
        not_not.mp (not_or.mp h).2⟩)
    rcases hna_or_hnb with hna | hnb
    · rw [if_neg hab, if_neg hna]
      simp
    · rw [if_neg hab, if_neg hnb]
      simp
private theorem char_prod_four (n : ℕ) (χ : MulChar (ZMod n) ℂ)
    (S : Finset ℕ) :
    (∏ p ∈ S, (χ (p : ZMod n)) ^ 4) =
      (χ ((∏ p ∈ S, p : ℕ) : ZMod n)) ^ 4 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
      simp [hp, ih, Nat.cast_mul, map_mul, mul_pow]
private theorem mask_prod (n : ℕ) (S : Finset ℕ) :
    (∏ p ∈ S, mask n p) = mask n (∏ p ∈ S, p) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [mask]
  | @insert p S hp ih =>
      simp [hp, ih]
      exact (mask_mul n p (∏ p ∈ S, p)).symm
end PoissonFirstLocal
open Finset Complex
namespace ActualCubicChar
variable {R F : Type*} [CommRing R] [IsDomain R] [Field F]
variable [Fintype F]
end ActualCubicChar
namespace ActualEisensteinCubic
section
open NumberField
end
end ActualEisensteinCubic
end
end OAI
end

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open OAI.PoissonFirstLocal
open scoped Classical
namespace OAI.PoissonFirstLocal
theorem _root_.solution
    (side : Bool) (P : Finset ℕ)
    (parityBit ε₁ ε₂ : ℕ → Bool)
    (n : ℕ) (χ : MulChar (ZMod n) ℂ) (hχ : χ ^ 6 = 1) :
    (∏ p ∈ P, oldFactor side (parityBit p) (ε₁ p) (ε₂ p) n p χ) =
      (χ ((∏ p ∈ P with retained (parityBit p) (ε₁ p) (ε₂ p), p : ℕ) : ZMod n)) ^ 4 *
      mask n (∏ p ∈ P with ¬retained (parityBit p) (ε₁ p) (ε₂ p), p) := by
  classical
  calc
    (∏ p ∈ P, oldFactor side (parityBit p) (ε₁ p) (ε₂ p) n p χ) =
        ∏ p ∈ P, newFactor (parityBit p) (ε₁ p) (ε₂ p) n p χ := by
          apply Finset.prod_congr rfl
          intro p hp
          exact first_local_identity side (parityBit p) (ε₁ p) (ε₂ p) n p χ hχ
    _ = (∏ p ∈ P with retained (parityBit p) (ε₁ p) (ε₂ p),
            (χ (p : ZMod n)) ^ 4) *
          (∏ p ∈ P with ¬retained (parityBit p) (ε₁ p) (ε₂ p), mask n p) := by
          simp only [newFactor]
          exact Finset.prod_ite _ _
    _ = _ := by
          rw [char_prod_four, mask_prod]
end OAI.PoissonFirstLocal
