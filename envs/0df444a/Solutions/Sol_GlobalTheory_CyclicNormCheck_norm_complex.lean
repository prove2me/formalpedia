-- Prove2me | solution 1 for GlobalTheory.CyclicNormCheck.norm_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:40:31.577484+00:00
-- url     : https://prove2.me/submissions/79ea7d7c-48fa-4302-865a-6df2141c1e9e

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_CyclicNormPrinciple
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_AdelicSplittingExamples_LocalConditionsOfGlobal
import Theorems.Thm_GlobalTheory_CyclicNormCheck_norm_of_root

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
theorem _root_.solution {F E : Type} [Field F] [Field E] [Algebra F E] [Algebra F ℂ]
    [Module.Finite F E] (a : ℂ) : ∃ y : ℂ ⊗[F] E, Algebra.norm ℂ y = a := by
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq a (Module.finrank_pos (R := F) (M := E))
  exact norm_of_root hr
end GlobalTheory.CyclicNormCheck
