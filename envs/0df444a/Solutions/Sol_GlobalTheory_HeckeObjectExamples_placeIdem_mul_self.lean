-- Prove2me | solution 1 for GlobalTheory.HeckeObjectExamples.placeIdem_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:15:46.717474+00:00
-- url     : https://prove2.me/submissions/6e5d3cf5-7d7e-485d-ab9d-308118ba41c6

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
theorem _root_.solution {v : HeightOneSpectrum (𝓞 F)} {ε : AF F}
    (h : IsPlaceIdem F v ε) : ε * ε = ε := by
  obtain ⟨α, rfl, h1, h0⟩ := h
  have : α * α = α := by
    apply RestrictedProduct.ext
    intro w
    change evalV F w (α * α) = evalV F w α
    rw [map_mul]
    by_cases hw : w = v
    · subst hw; rw [h1, one_mul]
    · rw [h0 w hw, mul_zero]
  change ((0 : Ainf F) * 0, α * α) = ((0 : Ainf F), α)
  rw [this, mul_zero]
end GlobalTheory.HeckeObjectExamples
