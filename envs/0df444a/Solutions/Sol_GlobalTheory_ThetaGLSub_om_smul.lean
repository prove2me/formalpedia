-- Prove2me | solution 1 for GlobalTheory.ThetaGLSub.om_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:31:19.399965+00:00
-- url     : https://prove2.me/submissions/b45d1df3-7756-4259-bb9e-184dfcbbac05

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
theorem _root_.solution (μ : kˣ →* ℂˣ) (g : GL (Fin m) k) (h : GL (Fin n) k) (c : ℂ) (Φ : Matrix (Fin n) (Fin m) k → ℂ) :
    om μ g h (c • Φ) = c • om μ g h Φ := by
  funext x; simp only [om, Pi.smul_apply, smul_eq_mul]; ring
end GlobalTheory.ThetaGLSub
