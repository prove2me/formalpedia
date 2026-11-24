-- Prove2me | solution 1 for GlobalTheory.ThetaGLSub.om_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:31:23.113145+00:00
-- url     : https://prove2.me/submissions/dd1dea26-3978-4b30-a5e7-a1527988eec6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsSubAug

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.SplitWeil
open GlobalTheory GlobalTheory.ThetaGLSub
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
variable {m : ℕ}
namespace GlobalTheory.ThetaGLSub
theorem _root_.solution (μ : kˣ →* ℂˣ) (g : GL (Fin m) k) (h : GL (Fin n) k) (Φ Ψ : Matrix (Fin n) (Fin m) k → ℂ) :
    om μ g h (Φ - Ψ) = om μ g h Φ - om μ g h Ψ := by
  funext x; simp only [om, Pi.sub_apply]; ring
end GlobalTheory.ThetaGLSub
