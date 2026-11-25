-- Prove2me | solution 1 for GlobalTheory.CyclicNormCheck.local_conditions_of_global
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:40:20.311569+00:00
-- url     : https://prove2.me/submissions/10188b73-e12f-483c-821b-5155f1417f08

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_CyclicNormPrinciple
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_AdelicSplittingExamples_LocalConditionsOfGlobal
import Theorems.Thm_GlobalTheory_CyclicNormCheck_norm_one_tmul_eq
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
theorem _root_.solution (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (x : F) (hx : x ≠ 0) (h : ∃ y : E, Algebra.norm F y = x) :
    (∀ v : HeightOneSpectrum (𝓞 F), ∃ y : TensorProduct F (v.adicCompletion F) E,
        Algebra.norm (v.adicCompletion F) y = algebraMap F (v.adicCompletion F) x) ∧
    (∀ σ : F →+* ℝ, (¬ ∃ τ : E →+* ℝ, τ.comp (algebraMap F E) = σ) → 0 < σ x) := by
  obtain ⟨y, rfl⟩ := h
  refine ⟨fun v => ⟨_, norm_one_tmul_eq y⟩, fun σ hσ => norm_pos_of_not_extends σ hσ ?_⟩
  rintro rfl
  exact hx (Algebra.norm_zero)
end GlobalTheory.CyclicNormCheck
