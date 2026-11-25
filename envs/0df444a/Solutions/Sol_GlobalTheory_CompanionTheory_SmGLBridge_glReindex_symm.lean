-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SmGLBridge.glReindex_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:58:07.368501+00:00
-- url     : https://prove2.me/submissions/c4afc76c-d4b0-4b58-bac1-3be33f60a73b

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
    (e : a ≃ b) (g : GL b k) : (glReindex (k := k) e).symm g = glReindex e.symm g := by
  apply Units.ext
  ext i j
  rfl
end GlobalTheory.CompanionTheory.SmGLBridge
