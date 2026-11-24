-- Prove2me | solution 1 for GlobalTheory.HasQExpansion.mdifferentiable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:49:45.021652+00:00
-- url     : https://prove2.me/submissions/95865f9b-6129-472b-abcb-056b9dfed546

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasQExpansionModularForm
import Theorems.Thm_GlobalTheory_HasQExpansion_exists_analytic

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
theorem _root_.solution (hh : 0 < h) (hf : HasQExpansion h f φ) : MDiff f := by
  obtain ⟨F, hF, -, hfF⟩ := hf.exists_analytic hh
  rw [UpperHalfPlane.mdifferentiable_iff]
  have : DifferentiableOn ℂ (fun z ↦ F (𝕢 h z)) {z : ℂ | 0 < z.im} := by
    intro z hz
    have h1 : DifferentiableAt ℂ F (𝕢 h z) :=
      (hF _ (by simpa using Periodic.norm_qParam_lt_one hh hz)).differentiableAt
    exact (h1.comp z (Periodic.differentiable_qParam z)).differentiableWithinAt
  refine this.congr fun z hz ↦ ?_
  simp [ofComplex_apply_of_im_pos hz, hfF]
end GlobalTheory.HasQExpansion
