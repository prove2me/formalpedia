-- Prove2me | solution 1 for GlobalTheory.ShortVectors.traceHerm_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:59.188826+00:00
-- url     : https://prove2.me/submissions/9f9d4dda-654d-4772-9247-435eda5dd557

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Transference
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_EmbeddingHermSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TraceHermNondegenerate
import Theorems.Thm_GlobalTheory_ShortVectors_traceHerm_apply
import Theorems.Thm_GlobalTheory_TraceDualMin_embedding_herm_self


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
theorem _root_.solution {n : ℕ} (x : Fin n → E) :
    (traceHerm n x x : ℝ) = ∑ σ : E →+* ℂ, ∑ k, ‖σ (x k)‖ ^ 2 := by
  rw [traceHerm_apply]
  have h1 := trace_eq_sum_embeddings (K := ℚ) (L := E) (E := ℂ) (x := herm 1 x x)
  have h2 : ∑ σ : E →ₐ[ℚ] ℂ, σ (herm 1 x x) = ∑ σ : E →+* ℂ, σ (herm 1 x x) :=
    (Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) _ _ fun σ => rfl).symm
  rw [h2] at h1
  simp only [TraceDualMin.embedding_herm_self] at h1
  apply Complex.ofReal_injective
  rw [Complex.ofReal_ratCast, ← eq_ratCast (algebraMap ℚ ℂ), h1, Complex.ofReal_sum]
end GlobalTheory.ShortVectors
