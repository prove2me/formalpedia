-- Prove2me | solution 1 for GlobalTheory.HasQExpansion.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:24:50.980787+00:00
-- url     : https://prove2.me/submissions/33f606c0-b316-460a-99e1-cb85cb48650c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasQExpansionModularForm
import Theorems.Thm_GlobalTheory_HasQExpansion_sub
import Theorems.Thm_GlobalTheory_HasQExpansion_eq_zero

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
theorem _root_.solution (hh : 0 < h) (hf : HasQExpansion h f φ) (hg : HasQExpansion h f ψ) : φ = ψ :=
  sub_eq_zero.mp (eq_zero hh (by simpa using hf.sub hg))
end GlobalTheory.HasQExpansion
