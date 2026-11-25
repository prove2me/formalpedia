-- Prove2me | solution 1 for GlobalTheory.normIntegers_properties_of_completeSpace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:56:35.461804+00:00
-- url     : https://prove2.me/submissions/e127ce03-9f62-4119-91cf-51a1905fbf6e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowLeComapMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Theorems.Thm_GlobalTheory_NormIntegers_isPrincipal_of_fg
import Theorems.Thm_GlobalTheory_NormIntegers_eq_bot_or_eq_span_of_fg_of_ne_top
import Theorems.Thm_GlobalTheory_NormIntegers_existsUnique_extend_of_fg
import Theorems.Thm_GlobalTheory_NormIntegers_ringKrullDim_eq_one
import Theorems.Thm_GlobalTheory_exists_norm_pow_eq_of_isAlgClosed
import Theorems.Thm_GlobalTheory_valueGroup_divisible_of_isAlgClosed
import Theorems.Thm_GlobalTheory_isLocalHom_of_comp_algebraMap_adicCompletion

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
theorem _root_.solution (C : Type*) [NontriviallyNormedField C]
    [IsUltrametricDist C] [CompleteSpace C] :
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
        g.comp (algebraMap A _) = f → IsLocalHom g) := by
  have hO := normIntegers_integers C
  refine ⟨fun w hw => NormIntegers.isAdicComplete_span_singleton hO hw,
    fun J hJ => NormIntegers.isPrincipal_of_fg hO hJ,
    fun J hJ hle => NormIntegers.eq_bot_or_eq_span_of_fg_of_ne_top hO hJ
      (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top hle),
    inferInstance, NormIntegers.ringKrullDim_eq_one hO,
    fun _ => ⟨fun γ n hn => valueGroup_divisible_of_isAlgClosed _ γ hn,
      fun x n hn => exists_norm_pow_eq_of_isAlgClosed x hn, inferInstance⟩,
    fun A _ _ _ f _ => ⟨NormIntegers.existsUnique_extend_of_fg hO
      (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing f,
      fun g hg => isLocalHom_of_comp_algebraMap_adicCompletion f g hg⟩⟩
end GlobalTheory
