-- Prove2me | solution 1 for GlobalTheory.CyclicNormCheck.neg_one_not_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:40:25.309796+00:00
-- url     : https://prove2.me/submissions/99d43b1e-bbb3-4639-a275-c908cde51f00

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_CyclicNormPrinciple
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_AdelicSplittingExamples_LocalConditionsOfGlobal
import Theorems.Thm_GlobalTheory_CyclicNormCheck_norm_pos_of_not_extends

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct
open GlobalTheory GlobalTheory.CyclicNormCheck
namespace GlobalTheory.CyclicNormCheck
theorem _root_.solution (E : Type) [Field E] [NumberField E] [IsCyclotomicExtension {4} ℚ E] :
    IsGalois ℚ E ∧ IsCyclic (E ≃ₐ[ℚ] E) ∧ Module.finrank ℚ E = 2 ∧ ¬ ∃ y : E, Algebra.norm ℚ y = -1 := by
  have hG : IsGalois ℚ E := IsCyclotomicExtension.isGalois {4} ℚ E
  have hr : Module.finrank ℚ E = 2 := by
    rw [IsCyclotomicExtension.finrank (n := 4) E (Polynomial.cyclotomic.irreducible_rat (by norm_num))]
    decide
  refine ⟨hG, isCyclic_of_prime_card (p := 2) (by rw [IsGalois.card_aut_eq_finrank, hr]), hr, ?_⟩
  rintro ⟨y, hy⟩
  have hσ : ¬ ∃ τ : E →+* ℝ, τ.comp (algebraMap ℚ _) = Rat.castHom ℝ := by
    rintro ⟨τ, -⟩
    have hζ := (IsCyclotomicExtension.zeta_spec 4 ℚ E).map_of_injective τ.injective
    have h2 := (hζ.pow (by norm_num) (show 4 = 2 * 2 by norm_num)).eq_neg_one_of_two_right
    nlinarith [sq_nonneg (τ (IsCyclotomicExtension.zeta 4 ℚ E))]
  have h0 : y ≠ 0 := by
    rintro rfl
    rw [Algebra.norm_zero] at hy
    norm_num at hy
  have := norm_pos_of_not_extends (Rat.castHom ℝ) hσ h0
  rw [hy] at this
  norm_num at this
end GlobalTheory.CyclicNormCheck
