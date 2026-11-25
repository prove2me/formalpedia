-- Prove2me | solution 1 for GlobalTheory.HeckeObjectExamples.idem_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:46:19.757667+00:00
-- url     : https://prove2.me/submissions/e82c1fae-3f52-449d-8dcd-2b7ccc325163

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_ThmBInHecke
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_AdelicSplittingExamples_LfacDenominatorNeZero
import Theorems.Thm_GlobalTheory_HeckeObjectExamples_placeIdem_mul_self

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
theorem _root_.solution {σ : E →ₐ[F] E} {P : HeightOneSpectrum (𝓞 E)} {e f : AE F E}
    (h : IsPrimeIdem σ P e f) : e * e = e := by
  rcases h with h | ⟨-, ⟨v, ε, hε, rfl⟩, -⟩
  · exact h.1.1.1
  · rw [← map_mul, placeIdem_mul_self hε]
end GlobalTheory.HeckeObjectExamples
