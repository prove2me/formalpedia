-- Prove2me | solution 1 for GlobalTheory.ThetaGLSub.om_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:31:18.058813+00:00
-- url     : https://prove2.me/submissions/22a3c16d-c7e8-4fb0-980f-8c8f015f49d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsSubAug
import Theorems.Thm_GlobalTheory_SplitWeil_Model_om_mul


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
theorem _root_.solution (μ : kˣ →* ℂˣ) (g : GL (Fin m) k) (h : GL (Fin n) k) (Φ : Matrix (Fin n) (Fin m) k → ℂ) :
    om μ g 1 (om μ 1 h Φ) = om μ 1 h (om μ g 1 Φ) := by
  simp only [← Model.om_mul, mul_one, one_mul]
end GlobalTheory.ThetaGLSub
