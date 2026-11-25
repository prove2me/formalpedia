-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.isSemisimple_prodMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:10:45.446703+00:00
-- url     : https://prove2.me/submissions/322535db-47ce-418d-baef-5582260f49a4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsSemisimpleOfISupEigenspace
import Theorems.Thm_GlobalTheory_WeilDeligne_isSemisimple_of_iSup_eigenspace
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
theorem _root_.solution [FiniteDimensional ℂ V] [FiniteDimensional ℂ V'] {f : End ℂ V}
    {g : End ℂ V'} (hf : f.IsSemisimple) (hg : g.IsSemisimple) :
    End.IsSemisimple (f.prodMap g : End ℂ (V × V')) := by
  refine isSemisimple_of_iSup_eigenspace ?_
  rw [eq_top_iff, ← Submodule.prod_top, ← hf.iSup_eigenspace_eq_top, ← hg.iSup_eigenspace_eq_top,
    LinearMap.prod_eq_sup_map, Submodule.map_iSup, Submodule.map_iSup]
  refine sup_le (iSup_mono fun α => ?_) (iSup_mono fun α => ?_)
  · rintro _ ⟨v, hv, rfl⟩
    simpa [End.mem_eigenspace_iff] using hv
  · rintro _ ⟨v, hv, rfl⟩
    simpa [End.mem_eigenspace_iff] using hv
end GlobalTheory.WeilDeligne
