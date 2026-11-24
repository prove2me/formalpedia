-- Prove2me | solution 1 for GlobalTheory.CyclicNormCheck.norm_real_of_extends
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:24:53.090215+00:00
-- url     : https://prove2.me/submissions/014a027c-2036-4368-90a5-16635075e130

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_CyclicNormPrinciple
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_AdelicSplittingExamples_LocalConditionsOfGlobal
import Theorems.Thm_GlobalTheory_CyclicNormCheck_norm_one_tmul_eq
import Theorems.Thm_GlobalTheory_CyclicNormCheck_norm_real_pos
import Theorems.Thm_GlobalTheory_CyclicNormCheck_exists_norm_neg

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
theorem _root_.solution {F E : Type} [Field F] [Field E] [Algebra F E] [Algebra F ℝ]
    [Module.Finite F E] [IsGalois F E] (τ : E →+* ℝ) (hτ : τ.comp (algebraMap F E) = algebraMap F ℝ)
    {a : ℝ} (ha : a ≠ 0) : ∃ y : ℝ ⊗[F] E, Algebra.norm ℝ y = a := by
  rcases ha.lt_or_gt with h | h
  · obtain ⟨y, hy⟩ := exists_norm_neg (F := F) τ
    have hy' : algebraMap F ℝ (Algebra.norm F y) < 0 := by rw [← hτ]; exact hy
    obtain ⟨z, hz⟩ := norm_real_pos (F := F) (E := E) (div_pos_of_neg_of_neg h hy')
    refine ⟨z * (1 ⊗ₜ y), ?_⟩
    rw [map_mul, hz, norm_one_tmul_eq, div_mul_cancel₀ _ hy'.ne]
  · exact norm_real_pos h
end GlobalTheory.CyclicNormCheck
