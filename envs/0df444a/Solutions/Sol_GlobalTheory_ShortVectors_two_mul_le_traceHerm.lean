-- Prove2me | solution 1 for GlobalTheory.ShortVectors.two_mul_le_traceHerm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:47:50.863465+00:00
-- url     : https://prove2.me/submissions/c3e40dde-240c-43a4-9785-85688d973afe

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Transference
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_EmbeddingHermSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TraceHermNondegenerate
import Theorems.Thm_GlobalTheory_ShortVectors_traceHerm_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD Module Submodule
open GlobalTheory
open GlobalTheory.ShortVectors
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.ShortVectors
theorem _root_.solution {n : ℕ} (x : Fin n → E) (τ : E →+* ℂ) :
    2 * ∑ k, ‖τ (x k)‖ ^ 2 ≤ (traceHerm n x x : ℝ) := by
  classical
  rw [traceHerm_self]
  let f : (E →+* ℂ) → ℝ := fun σ => ∑ k, ‖σ (x k)‖ ^ 2
  have hne : NumberField.ComplexEmbedding.conjugate τ ≠ τ := by
    intro h
    have hr : NumberField.ComplexEmbedding.IsReal τ := NumberField.ComplexEmbedding.isReal_iff.mpr h
    exact NumberField.InfinitePlace.not_isReal_of_mk_isComplex
      (NumberField.IsTotallyComplex.isComplex (NumberField.InfinitePlace.mk τ)) hr
  have hf : f (NumberField.ComplexEmbedding.conjugate τ) = f τ := by
    simp [f, NumberField.ComplexEmbedding.conjugate_coe_eq]
  have hnn : ∀ σ ∈ (Finset.univ : Finset (E →+* ℂ)), σ ∉ ({τ, NumberField.ComplexEmbedding.conjugate τ} : Finset _) →
      0 ≤ f σ := fun σ _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc 2 * ∑ k, ‖τ (x k)‖ ^ 2 = f τ + f (NumberField.ComplexEmbedding.conjugate τ) := by
        rw [hf]; ring
    _ = ∑ σ ∈ ({τ, NumberField.ComplexEmbedding.conjugate τ} : Finset _), f σ := by
        rw [Finset.sum_pair hne.symm]
    _ ≤ ∑ σ, f σ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) hnn
end GlobalTheory.ShortVectors
