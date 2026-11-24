-- Prove2me | solution 1 for GlobalTheory.ThetaGLSub.om_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:20.973796+00:00
-- url     : https://prove2.me/submissions/f16e19ac-cc5d-414c-b48d-75aa7cc36a6a

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
    om μ g h (Φ + Ψ) = om μ g h Φ + om μ g h Ψ := by
  funext x; simp only [om, Pi.add_apply]; ring
end GlobalTheory.ThetaGLSub
