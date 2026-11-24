-- Prove2me | solution 1 for GlobalTheory.HasQExpansion.of_periodic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:14:20.708804+00:00
-- url     : https://prove2.me/submissions/a2de927a-6193-4cd7-8c08-9ccf69004861

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasQExpansionModularForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperHalfPlane ModularForm Complex Function Filter PowerSeries
open scoped Topology MatrixGroups Manifold Real
noncomputable section
open GlobalTheory
local notation "𝕢" => Function.Periodic.qParam
open GlobalTheory.HasQExpansion
variable {h : ℝ} {f g : ℍ → ℂ} {φ ψ : PowerSeries ℂ}
namespace GlobalTheory.HasQExpansion
theorem _root_.solution (hh : 0 < h) (hper : Periodic (f ∘ ofComplex) h) (hhol : MDiff f)
    (hbdd : IsBoundedAtImInfty f) : HasQExpansion h f (qExpansion h f) := fun τ ↦ by
  simpa using UpperHalfPlane.hasSum_qExpansion hh hper hhol hbdd τ
end GlobalTheory.HasQExpansion
