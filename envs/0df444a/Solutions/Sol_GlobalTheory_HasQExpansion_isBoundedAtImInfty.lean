-- Prove2me | solution 1 for GlobalTheory.HasQExpansion.isBoundedAtImInfty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:04:44.645844+00:00
-- url     : https://prove2.me/submissions/bdad8ee1-5547-407a-9805-9581a5dd0ced

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasQExpansionModularForm
import Theorems.Thm_GlobalTheory_HasQExpansion_tendsto

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
theorem _root_.solution (hh : 0 < h) (hf : HasQExpansion h f φ) : IsBoundedAtImInfty f :=
  (hf.tendsto hh).isBigO_one ℝ
end GlobalTheory.HasQExpansion
