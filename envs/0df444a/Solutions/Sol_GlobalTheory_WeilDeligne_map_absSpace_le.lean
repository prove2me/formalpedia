-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.map_absSpace_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:58:35.636171+00:00
-- url     : https://prove2.me/submissions/21771485-f6f1-4ed3-9459-defa32305424

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsSemisimpleOfISupEigenspace
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
theorem _root_.solution {f : End ℂ V} {g : End ℂ V'} (e : V →ₗ[ℂ] V') (he : ∀ v, e (f v) = g (e v))
    (r : ℝ) : (absSpace f r).map e ≤ absSpace g r := by
  simp only [absSpace, Submodule.map_iSup]
  refine iSup₂_mono fun α _ => ?_
  rintro _ ⟨v, hv, rfl⟩
  rw [SetLike.mem_coe, End.mem_eigenspace_iff] at hv
  rw [End.mem_eigenspace_iff, ← he, hv, map_smul]
end GlobalTheory.WeilDeligne
