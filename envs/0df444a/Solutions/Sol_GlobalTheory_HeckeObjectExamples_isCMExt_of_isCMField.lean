-- Prove2me | solution 1 for GlobalTheory.HeckeObjectExamples.isCMExt_of_isCMField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:46:24.690353+00:00
-- url     : https://prove2.me/submissions/e0ed9bfa-1a44-4815-9a90-f17da8502cd9

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_ThmBInHecke
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_AdelicSplittingExamples_LfacDenominatorNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open NumberField IsDedekindDomain HeckeCharacterZeroLocus.ThmBIn
open GlobalTheory GlobalTheory.HeckeObjectExamples
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace GlobalTheory.HeckeObjectExamples
theorem _root_.solution (K : Type) [Field K] [NumberField K] [IsCMField K] :
    IsCMExt (maximalRealSubfield K) K (IsCMField.complexConj K).toAlgHom :=
  ⟨inferInstance, inferInstance, Algebra.IsQuadraticExtension.finrank_eq_two _ _,
    fun τ x => IsCMField.complexEmbedding_complexConj K τ x⟩
end GlobalTheory.HeckeObjectExamples
