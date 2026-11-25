-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.mem_absSpace_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:20:32.210742+00:00
-- url     : https://prove2.me/submissions/9e62e220-753e-4d2f-a401-7a85b97df43b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsSemisimpleOfISupEigenspace
import Theorems.Thm_GlobalTheory_WeilDeligne_map_absSpace_le
import Theorems.Thm_GlobalTheory_WeilDeligne_coe_qPow
import Theorems.Thm_GlobalTheory_WeilDeligne_deg_ineIncl
import Theorems.Thm_GlobalTheory_WeilDeligne_qPow_zero
import Theorems.Thm_GlobalTheory_WeilDeligne_unrChar_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeilDeligne.coe_qPow
attribute [local simp] GlobalTheory.WeilDeligne.deg_ineIncl
attribute [local simp] GlobalTheory.WeilDeligne.qPow_zero
attribute [local simp] GlobalTheory.WeilDeligne.unrChar_apply



set_option autoImplicit false
noncomputable section
open Polynomial TensorProduct Module
open GlobalTheory GlobalTheory.WeilDeligne
variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
namespace GlobalTheory.WeilDeligne
theorem _root_.solution {f : End ℂ V} {g : End ℂ V'} (e : V ≃ₗ[ℂ] V')
    (he : ∀ v, e (f v) = g (e v)) (r : ℝ) (v : V) : e v ∈ absSpace g r ↔ v ∈ absSpace f r := by
  refine ⟨fun hv => ?_, fun hv => map_absSpace_le e.toLinearMap he r ⟨v, hv, rfl⟩⟩
  have := map_absSpace_le (f := g) (g := f) e.symm.toLinearMap
    (fun x => by simp [e.symm_apply_eq, he]) r ⟨_, hv, rfl⟩
  simpa using this
end GlobalTheory.WeilDeligne
