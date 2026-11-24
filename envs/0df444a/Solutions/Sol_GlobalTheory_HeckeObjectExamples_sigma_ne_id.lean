-- Prove2me | solution 1 for GlobalTheory.HeckeObjectExamples.sigma_ne_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:14:17.139392+00:00
-- url     : https://prove2.me/submissions/b39d610d-9106-404f-bc0e-c77dc29455f7

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
theorem _root_.solution {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : σ ≠ AlgHom.id F E := by
  intro hσ
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have := h.2.1
  apply IsTotallyComplex.complexEmbedding_not_isReal τ
  rw [ComplexEmbedding.isReal_iff]
  ext x
  have := h.2.2.2 τ x
  rw [hσ] at this
  simpa [ComplexEmbedding.conjugate_coe_eq] using this.symm
end GlobalTheory.HeckeObjectExamples
