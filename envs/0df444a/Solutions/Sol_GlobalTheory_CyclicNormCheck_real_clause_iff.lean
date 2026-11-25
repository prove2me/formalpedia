-- Prove2me | solution 1 for GlobalTheory.CyclicNormCheck.real_clause_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:40:38.463752+00:00
-- url     : https://prove2.me/submissions/990f93fa-df8c-4364-a2b8-1147f2b3c54e

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_CyclicNormPrinciple
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_AdelicSplittingExamples_LocalConditionsOfGlobal
import Theorems.Thm_GlobalTheory_CyclicNormCheck_norm_real_pos
import Theorems.Thm_GlobalTheory_CyclicNormCheck_norm_real_of_extends
import Theorems.Thm_GlobalTheory_CyclicNormCheck_local_norm_nonneg

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
theorem _root_.solution {F E : Type} [Field F] [Field E] [Algebra F E] [Algebra F ℝ] [CharZero F]
    [Module.Finite F E] [IsGalois F E] {x : F} (hx : x ≠ 0) :
    ((¬ ∃ τ : E →+* ℝ, τ.comp (algebraMap F E) = algebraMap F ℝ) → 0 < algebraMap F ℝ x) ↔
      ∃ y : ℝ ⊗[F] E, Algebra.norm ℝ y = algebraMap F ℝ x := by
  have hx' : algebraMap F ℝ x ≠ 0 := (map_ne_zero _).2 hx
  constructor
  · intro h
    by_cases hσ : ∃ τ : E →+* ℝ, τ.comp (algebraMap F E) = algebraMap F ℝ
    · obtain ⟨τ, hτ⟩ := hσ
      exact norm_real_of_extends τ hτ hx'
    · exact norm_real_pos (h hσ)
  · rintro ⟨y, hy⟩ hσ
    exact lt_of_le_of_ne (hy ▸ local_norm_nonneg hσ y) hx'.symm
end GlobalTheory.CyclicNormCheck
