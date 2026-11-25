-- Prove2me | solution 1 for GlobalTheory.RealWeil.exists_schwartz_rhoFun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:42:42.989196+00:00
-- url     : https://prove2.me/submissions/3c00f7a3-4717-4707-97dd-83e7905f9a5e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzTranslate
import Theorems.Thm_GlobalTheory_RealWeil_coe_rhoSch

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.RealWeil MeasureTheory Complex
open scoped SchwartzMap Matrix Real RealInnerProductSpace
open GlobalTheory GlobalTheory.RealWeil
variable {l : Type} [Fintype l]
namespace GlobalTheory.RealWeil
theorem _root_.solution : ∀ (l : Type) [Fintype l] (w : l ⊕ l → ℝ) (f : Sch l), ∃ f₁ : Sch l, ⇑f₁ = rhoFun w ⇑f :=
  fun _ _ w f => ⟨rhoSch w f, coe_rhoSch w f⟩
end GlobalTheory.RealWeil
