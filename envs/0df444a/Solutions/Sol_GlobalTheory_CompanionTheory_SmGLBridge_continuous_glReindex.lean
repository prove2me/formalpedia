-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SmGLBridge.continuous_glReindex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:03:08.156748+00:00
-- url     : https://prove2.me/submissions/a96302dc-07c5-470d-8067-4145e72ecd1e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IrreducibleSmoothAdmissibleGL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmGLBridge
variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k]
namespace GlobalTheory.CompanionTheory.SmGLBridge
theorem _root_.solution {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (e : a ≃ b) : Continuous (glReindex (k := k) e) := by
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · show Continuous fun g : GL a k => Matrix.reindex e e (g : Matrix a a k)
    exact Units.continuous_val.matrix_reindex e e
  · show Continuous fun g : GL a k => Matrix.reindex e e ((g⁻¹ : GL a k) : Matrix a a k)
    exact Units.continuous_coe_inv.matrix_reindex e e
end GlobalTheory.CompanionTheory.SmGLBridge
