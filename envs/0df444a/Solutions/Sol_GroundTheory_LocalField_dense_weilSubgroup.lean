-- Prove2me | solution 1 for GroundTheory.LocalField.dense_weilSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:37:03.188418+00:00
-- url     : https://prove2.me/submissions/55ac76b0-2123-46a7-97f0-a10a8c450f08

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramified
import Definitions.Def_GroundTheory_LocalFields_WeilGroupDefs
import Theorems.Thm_GroundTheory_LocalField_restrictNormal_eq_frobenius_zpow_iff
import Theorems.Thm_GroundTheory_LocalField_exists_restrictNormal_eq_frobenius_zpow
import Theorems.Thm_GroundTheory_LocalField_dense_zpowers_ofAdd_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel IntermediateField GroundTheory.LocalField.Abstract Topology
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
namespace GroundTheory.LocalField
theorem _root_.solution : Dense (weilSubgroup K Ω : Set (Ω ≃ₐ[K] Ω)) := by
  have : T2Space (Ω ≃ₐ[K] Ω) := krullTopology_t2
  set C := (weilSubgroup K Ω).topologicalClosure with hC
  have hCc : IsCompact (C : Set (Ω ≃ₐ[K] Ω)) := (Subgroup.isClosed_topologicalClosure _).isCompact
  have himc : IsClosed (unramifiedDegree K Ω '' (C : Set (Ω ≃ₐ[K] Ω))) :=
    (hCc.image continuous_unramifiedDegree).isClosed
  have hsub : (Subgroup.zpowers (Multiplicative.ofAdd (1 : ℤ̂)) : Set (Multiplicative ℤ̂)) ⊆
      unramifiedDegree K Ω '' (C : Set (Ω ≃ₐ[K] Ω)) := by
    rintro _ ⟨n, rfl⟩
    obtain ⟨σ, hσ⟩ := exists_restrictNormal_eq_frobenius_zpow K Ω n
    refine ⟨σ, (weilSubgroup K Ω).le_topologicalClosure (mem_weilSubgroup_iff.2 ⟨n, hσ⟩), ?_⟩
    show _ = Multiplicative.ofAdd 1 ^ n
    rw [(restrictNormal_eq_frobenius_zpow_iff σ n).1 hσ, ← ofAdd_zsmul, zsmul_one]
  have huniv : unramifiedDegree K Ω '' (C : Set (Ω ≃ₐ[K] Ω)) = Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← dense_zpowers_ofAdd_one.closure_eq]
    exact himc.closure_subset_iff.2 hsub
  rw [dense_iff_closure_eq, ← Subgroup.topologicalClosure_coe, ← hC]
  refine Set.eq_univ_of_forall fun τ ↦ ?_
  obtain ⟨c, hc, hcτ⟩ : unramifiedDegree K Ω τ ∈ unramifiedDegree K Ω '' (C : Set (Ω ≃ₐ[K] Ω)) := by
    rw [huniv]; trivial
  have hk : c⁻¹ * τ ∈ (unramifiedDegree K Ω).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hcτ, inv_mul_cancel]
  rw [ker_unramifiedDegree] at hk
  have hk' : c⁻¹ * τ ∈ C :=
    (weilSubgroup K Ω).le_topologicalClosure (fixingSubgroup_le_weilSubgroup K Ω hk)
  have := C.mul_mem hc hk'
  rwa [mul_inv_cancel_left] at this
end GroundTheory.LocalField
