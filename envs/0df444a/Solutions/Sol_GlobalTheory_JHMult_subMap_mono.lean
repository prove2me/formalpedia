-- Prove2me | solution 1 for GlobalTheory.JHMult.subMap_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:30:44.066169+00:00
-- url     : https://prove2.me/submissions/e3ac1fac-b336-46d3-b0d7-d336f553f453

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_JhMultSubAddQuot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
open GlobalTheory GlobalTheory.JHMult
variable {F G V W V₁ V₂ : Type} [Field F] [Group G] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂]
namespace GlobalTheory.JHMult
theorem _root_.solution {ρ : Representation F G V} {ρ₁ : Representation F G V₁}
    (p : ρ.IntertwiningMap ρ₁) {S T : Subrepresentation ρ} (h : S ≤ T) : subMap p S ≤ subMap p T := by
  rintro _ ⟨v, hv, rfl⟩
  exact ⟨v, h hv, rfl⟩
end GlobalTheory.JHMult
