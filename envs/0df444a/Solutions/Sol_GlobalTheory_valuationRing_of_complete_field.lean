-- Prove2me | solution 1 for GlobalTheory.valuationRing_of_complete_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:42:51.121455+00:00
-- url     : https://prove2.me/submissions/89d95bd2-abb9-4509-bc6d-fcc9fca1b736

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowLeComapMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Theorems.Thm_GlobalTheory_exists_complete_isAlgClosed_of_isDiscreteValuationRing
import Theorems.Thm_GlobalTheory_exists_complete_isAlgClosed_padic_of_isDiscreteValuationRing
import Theorems.Thm_GlobalTheory_normIntegers_properties_of_completeSpace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
universe u
namespace GlobalTheory
theorem _root_.solution :
    (∀ (C : Type u) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C],
      (∀ w : normIntegers C, ‖(w : C)‖ < 1 → IsAdicComplete (Ideal.span {w}) (normIntegers C)) ∧
      (∀ J : Ideal (normIntegers C), J.FG → J.IsPrincipal) ∧
      (∀ J : Ideal (normIntegers C), J.FG → J ≤ IsLocalRing.maximalIdeal (normIntegers C) →
        J = ⊥ ∨ ∃ w : normIntegers C, 0 < ‖(w : C)‖ ∧ ‖(w : C)‖ < 1 ∧ J = Ideal.span {w}) ∧
      HenselianLocalRing (normIntegers C) ∧
      ringKrullDim (normIntegers C) = 1 ∧
      (IsAlgClosed C →
        (∀ (γ : (normIntegers C).ValueGroup) (n : ℕ), 0 < n → ∃ δ, δ ^ n = γ) ∧
        (∀ (x : C) (n : ℕ), 0 < n → ∃ y : C, ‖y‖ ^ n = ‖x‖) ∧
        IsAlgClosed (IsLocalRing.ResidueField (normIntegers C))) ∧
      (∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
        (f : A →+* normIntegers C) [IsLocalHom f],
        (∃! g : AdicCompletion (IsLocalRing.maximalIdeal A) A →+* normIntegers C,
          g.comp (algebraMap A _) = f) ∧
        ∀ g : AdicCompletion (IsLocalRing.maximalIdeal A) A →+* normIntegers C,
          g.comp (algebraMap A _) = f → IsLocalHom g)) ∧
    (∀ (V K : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K]
      [Algebra V K] [IsFractionRing V K],
      (∀ a : V, a ≠ 0 → a ∈ IsLocalRing.maximalIdeal V → ∀ r : ℝ, 0 < r → r < 1 →
        ∃ (C : Type u) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C)
          (_ : CompleteSpace C) (_ : IsAlgClosed C) (_ : Algebra K C),
          (∀ x : K, ‖algebraMap K C x‖ ≤ 1 ↔ x ∈ (algebraMap V K).range) ∧
            ‖algebraMap K C (algebraMap V K a)‖ = r) ∧
      (∀ [CharZero K] (p : ℕ) [Fact p.Prime], (p : V) ∈ IsLocalRing.maximalIdeal V →
        ∃ (C : Type u) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C)
          (_ : CompleteSpace C) (_ : IsAlgClosed C) (_ : NormedAlgebra ℚ_[p] C) (_ : Algebra K C),
          ∀ x : K, ‖algebraMap K C x‖ ≤ 1 ↔ x ∈ (algebraMap V K).range)) :=
  ⟨fun C _ _ _ => normIntegers_properties_of_completeSpace C,
    fun V K _ _ _ _ _ _ =>
      ⟨fun _ ha0 ha _ hr0 hr1 =>
        exists_complete_isAlgClosed_of_isDiscreteValuationRing V K ha0 ha hr0 hr1,
      fun p _ hp => exists_complete_isAlgClosed_padic_of_isDiscreteValuationRing V K p hp⟩⟩
end GlobalTheory
