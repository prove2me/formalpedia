-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TfLoc.Iw.val_aut_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:41:19.063524+00:00
-- url     : https://prove2.me/submissions/85e89017-2675-4b57-8ad8-2fe6bfa5af15

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriFactorization

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
theorem _root_.solution (τ : E ≃ₐ[k] E) {x : E} (hx : valuation E x ≤ 1) :
    valuation E (τ x) ≤ 1 := by
  have h := (GroundTheory.LocalField.isIntegral_iff k E x).2 hx
  exact (GroundTheory.LocalField.isIntegral_iff k E (τ x)).1
    (h.map ((τ : E →ₐ[k] E).restrictScalars 𝒪[k]))
end GlobalTheory.CompanionTheory.TfLoc.Iw
