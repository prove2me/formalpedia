-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TfLoc.Iw.val_aut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:39:38.285529+00:00
-- url     : https://prove2.me/submissions/a091dcb9-6734-4b2d-aaeb-1c09f86c6776

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriFactorization
import Theorems.Thm_GlobalTheory_CompanionTheory_TfLoc_Iw_not_val_lt_val_aut

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel PositivityTheory.Rg.Tf.Loc Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TfLoc GlobalTheory.CompanionTheory.TfLoc.Iw
variable {k E : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E]
namespace GlobalTheory.CompanionTheory.TfLoc.Iw
theorem _root_.solution [IsGalois k E] (τ : E ≃ₐ[k] E) (x : E) : valuation E (τ x) = valuation E x := by
  refine le_antisymm (not_lt.1 (not_val_lt_val_aut τ x)) (not_lt.1 ?_)
  have := not_val_lt_val_aut τ⁻¹ (τ x)
  simpa using this
end GlobalTheory.CompanionTheory.TfLoc.Iw
