-- Prove2me | solution 1 for GlobalTheory.PrinTwo.ev_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:11:37.178508+00:00
-- url     : https://prove2.me/submissions/fe947013-c523-4a66-9177-da613708ef43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WEMulNUMulTD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct
open GlobalTheory GlobalTheory.PrinTwo
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.PrinTwo
theorem _root_.solution {μ₁ μ₂ : kˣ →* ℂˣ} (f f' : PSp μ₁ μ₂) (g : GL (Fin (1 + 1)) k) :
    ev (f - f') g = ev f g - ev f' g := by
  show TensorProduct.lid ℂ ℂ (f.1.1 g - f'.1.1 g) = _
  rw [map_sub]; rfl
end GlobalTheory.PrinTwo
