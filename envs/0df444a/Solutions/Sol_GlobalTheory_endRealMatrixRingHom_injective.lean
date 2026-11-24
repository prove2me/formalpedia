-- Prove2me | solution 1 for GlobalTheory.endRealMatrixRingHom_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:37:05.486802+00:00
-- url     : https://prove2.me/submissions/896e81ab-01f9-45fe-8b3d-48bb2a499fdd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RationalMatrixIdentityTransferToComplexMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {g n : ℕ} (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)) :
    Function.Injective (endRealMatrixRingHom e) := by
  intro f h hfh
  have h1 : f.restrictScalars ℝ = h.restrictScalars ℝ := (LinearMap.toMatrix e e).injective hfh
  exact LinearMap.restrictScalars_injective ℝ h1
end GlobalTheory
