-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.mem_absSpace_diagEnd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:57:42.503561+00:00
-- url     : https://prove2.me/submissions/e4335847-aed4-44f4-a5cb-6702ea34bd86

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
theorem _root_.solution {ι : Type*} [Finite ι] (c : ι → ℂ) (r : ℝ) (v : ι → ℂ) :
    v ∈ absSpace (diagEnd c) r ↔ ∀ i, ‖c i‖ ≠ r → v i = 0 := by
  classical
  have := Fintype.ofFinite ι
  constructor
  · intro hv i hi
    have hle : absSpace (diagEnd c) r ≤ LinearMap.ker (LinearMap.proj i : (ι → ℂ) →ₗ[ℂ] ℂ) := by
      refine iSup₂_le fun α hα u hu => ?_
      have h1 := congrFun (End.mem_eigenspace_iff.mp hu) i
      simp only [diagEnd_apply, Pi.smul_apply, smul_eq_mul] at h1
      have h2 : c i ≠ α := fun h => hi (h ▸ hα)
      simpa [h2] using h1
    exact hle hv
  · intro hv
    rw [← Finset.univ_sum_single v]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : ‖c i‖ = r
    · refine Submodule.mem_iSup_of_mem (c i) (Submodule.mem_iSup_of_mem hi ?_)
      rw [End.mem_eigenspace_iff]
      ext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
    · simp [hv i hi]
end GlobalTheory.WeilDeligne
