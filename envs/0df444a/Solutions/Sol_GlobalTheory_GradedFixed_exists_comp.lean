-- Prove2me | solution 1 for GlobalTheory.GradedFixed.exists_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:36:22.509963+00:00
-- url     : https://prove2.me/submissions/a6b01d4f-a833-4da0-a09d-958a899b4895

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_FixedMemOfOrbitHeight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Submodule MulAction
open GlobalTheory GlobalTheory.GradedFixed
variable {G ι M : Type} [Group G] [MulAction G ι] [AddCommGroup M] [Module ℂ M]
namespace GlobalTheory.GradedFixed
theorem _root_.solution (V : ι → Submodule ℂ M) (hV : iSupIndep V) (htop : (⨆ i, V i) = ⊤) :
    ∃ c : ι → M →ₗ[ℂ] M, (∀ i w, c i w ∈ V i) ∧ (∀ i v, v ∈ V i → c i v = v) ∧
      (∀ i j v, i ≠ j → v ∈ V j → c i v = 0) ∧ (∀ w, ∃ F : Finset ι, w = ∑ i ∈ F, c i w) := by
  classical
  letI := (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hV htop).chooseDecomposition
  refine ⟨fun i => (V i).subtype ∘ₗ (DirectSum.component ℂ ι (fun i => ↥(V i)) i) ∘ₗ
    (DirectSum.decomposeLinearEquiv V).toLinearMap, ?_, ?_, ?_, ?_⟩
  · intro i w; simp
  · intro i v hv
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.subtype_apply,
      ← DirectSum.apply_eq_component, DirectSum.decomposeLinearEquiv_apply]
    exact DirectSum.decompose_of_mem_same V hv
  · intro i j v hij hv
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.subtype_apply,
      ← DirectSum.apply_eq_component, DirectSum.decomposeLinearEquiv_apply]
    exact DirectSum.decompose_of_mem_ne V hv hij.symm
  · intro w
    refine ⟨(DirectSum.decompose V w).support, ?_⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.subtype_apply,
      ← DirectSum.apply_eq_component, DirectSum.decomposeLinearEquiv_apply]
    exact (DirectSum.sum_support_decompose V w).symm
end GlobalTheory.GradedFixed
