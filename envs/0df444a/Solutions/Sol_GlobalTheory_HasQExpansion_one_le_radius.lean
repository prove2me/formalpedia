-- Prove2me | solution 1 for GlobalTheory.HasQExpansion.one_le_radius
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:14:21.524704+00:00
-- url     : https://prove2.me/submissions/c1fac5fc-129f-4bac-8f59-dbf155e05ad3

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
theorem _root_.solution (hh : 0 < h) (hf : HasQExpansion h f φ) :
    1 ≤ (FormalMultilinearSeries.ofScalars ℂ (fun m ↦ coeff m φ)).radius := by
  refine le_of_forall_lt_imp_le_of_dense fun r hr ↦ ?_
  rcases eq_or_ne r 0 with rfl | hr'
  · simp
  · lift r to NNReal using hr.ne_top
    apply FormalMultilinearSeries.le_radius_of_summable
    have hq : ‖((r : ℝ) : ℂ)‖ < 1 := by simpa using hr
    have hq1 : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr'
    have h1 := Periodic.im_invQParam_pos_of_norm_lt_one hh hq hq1
    have := (hf ⟨_, h1⟩).summable.norm
    simp only [Periodic.qParam_right_inv hh.ne' hq1] at this
    simpa [norm_mul] using this
end GlobalTheory.HasQExpansion
