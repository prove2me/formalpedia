-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.IsCompactModCenter.mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:45:54.365801+00:00
-- url     : https://prove2.me/submissions/a210c31e-211a-4b81-8fa3-1c8d04fc349a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SupercuspidalCoefficients
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingSums

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Function
open scoped Pointwise
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
omit [ValuativeRel F] [IsNonarchimedeanLocalField F]
namespace GroundTheory.Automorphic.Parabolic
namespace IsCompactModCenter
theorem _root_.solution {φ ψ : GL (Fin n) F → ℂ} (hφ : IsCompactModCenter φ)
    (h : support ψ ⊆ support φ) : IsCompactModCenter ψ := by
  obtain ⟨C, hC, hsupp⟩ := hφ
  exact ⟨C, hC, h.trans hsupp⟩
end IsCompactModCenter
end GroundTheory.Automorphic.Parabolic
