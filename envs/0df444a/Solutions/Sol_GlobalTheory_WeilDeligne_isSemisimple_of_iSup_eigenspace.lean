-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.isSemisimple_of_iSup_eigenspace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:57:11.730959+00:00
-- url     : https://prove2.me/submissions/efef2a64-bdc0-4a46-874f-a26fd2c7a3c1

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
theorem _root_.solution [FiniteDimensional ℂ V] {f : End ℂ V}
    (hf : ⨆ α, f.eigenspace α = ⊤) : f.IsSemisimple := by
  classical
  have hfin : Set.Finite {α : ℂ | f.HasEigenvalue α} := Module.End.finite_hasEigenvalue f
  refine End.isSemisimple_of_squarefree_aeval_eq_zero (p := ∏ α ∈ hfin.toFinset, (X - C α))
    (separable_prod_X_sub_C_iff'.mpr fun _ _ _ _ h => h).squarefree ?_
  rw [← LinearMap.ker_eq_top, eq_top_iff, ← hf]
  refine iSup_le fun α v hv => ?_
  by_cases hα : f.HasEigenvalue α
  · rw [LinearMap.mem_ker, ← Finset.prod_erase_mul _ _ (hfin.mem_toFinset.mpr hα), map_mul,
      End.mul_apply]
    have : aeval f (X - C α) v = 0 := by
      simp [End.mem_eigenspace_iff.mp hv]
    rw [this, map_zero]
  · rw [End.hasEigenvalue_iff, not_not] at hα
    rw [hα, Submodule.mem_bot] at hv
    rw [hv]; exact zero_mem _
end GlobalTheory.WeilDeligne
