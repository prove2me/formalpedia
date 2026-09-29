-- Prove2me | solution 1 for LinearMap.exists_injective_comp_eq_smul_of_forall_exists_smul_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/1915e850-2f55-5094-ba2a-a38da2a74d87

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LinearMap_exists_injective_comp_eq_smul_of_forall_exists_smul_mem_range

set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪]
    {R : Type} [CommRing R] [Algebra 𝒪 R]
    {V : Type} [AddCommGroup V] [Module R V] [Module 𝒪 V] [IsScalarTower 𝒪 R V] [Module.Finite 𝒪 V]
    {Y : Type} [AddCommGroup Y] [Module R Y] [Module 𝒪 Y] [IsScalarTower 𝒪 R Y]
    {M : Type} [AddCommGroup M] [Module R M] [Module 𝒪 M] [IsScalarTower 𝒪 R M]
    (htf : ∀ (a : 𝒪) (m : M), a ≠ 0 → a • m = 0 → m = 0)
    (ι : Y →ₗ[R] M) (hι : Function.Injective ι)
    (hloc : ∀ m : M, ∃ a : 𝒪, a ≠ 0 ∧ a • m ∈ LinearMap.range ι)
    (J : V →ₗ[R] M) (hJ : Function.Injective J) :
    ∃ (a : 𝒪) (_ : a ≠ 0) (j : V →ₗ[R] Y), Function.Injective j ∧ ∀ v : V, ι (j v) = a • J v := by
  classical

  obtain ⟨s, hs⟩ := Module.finite_def.mp (inferInstance : Module.Finite 𝒪 V)
  choose c hc0 hc using fun m : M => hloc m
  set a : 𝒪 := ∏ v ∈ s, c (J v) with ha_def
  have ha : a ≠ 0 := by rw [ha_def]; exact Finset.prod_ne_zero_iff.mpr fun v _ => hc0 (J v)

  let N : Submodule 𝒪 M := (LinearMap.range ι).restrictScalars 𝒪
  have hN_smul : ∀ (b : 𝒪) (m : M), m ∈ N → b • m ∈ N := fun b m hm => N.smul_mem b hm
  let T : V →ₗ[𝒪] M := a • J.restrictScalars 𝒪
  have hT : ∀ v, T v = a • J v := fun v => rfl
  have hgen : ∀ v ∈ s, T v ∈ N := by
    intro v hv
    rw [hT, ha_def, ← Finset.prod_erase_mul s (fun w => c (J w)) hv, mul_smul]
    exact hN_smul _ _ (hc (J v))
  have hall : ∀ v : V, a • J v ∈ LinearMap.range ι := by
    have hle : (⊤ : Submodule 𝒪 V) ≤ N.comap T := by
      rw [← hs, Submodule.span_le]
      intro v hv
      exact hgen v hv
    intro v
    exact hle (Submodule.mem_top (x := v))

  let K : V →ₗ[R] M := (algebraMap 𝒪 R a) • J
  have hK : ∀ v, K v = a • J v := fun v => by
    show (algebraMap 𝒪 R a) • J v = a • J v
    exact algebraMap_smul R a (J v)
  have hKr : ∀ v, K v ∈ LinearMap.range ι := fun v => by rw [hK]; exact hall v
  let e := LinearEquiv.ofInjective ι hι
  let j : V →ₗ[R] Y := e.symm.toLinearMap ∘ₗ LinearMap.codRestrict (LinearMap.range ι) K hKr
  have hj : ∀ v, ι (j v) = a • J v := by
    intro v
    have h1 : (e (j v) : M) = (LinearMap.codRestrict (LinearMap.range ι) K hKr v : M) := by
      simp only [j, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.apply_symm_apply]
    rw [LinearEquiv.ofInjective_apply, LinearMap.codRestrict_apply] at h1
    rw [h1, hK]
  refine ⟨a, ha, j, ?_, hj⟩
  intro v w hvw
  have h := congrArg ι hvw
  rw [hj, hj, ← sub_eq_zero, ← smul_sub, ← map_sub] at h
  have := htf a _ ha h
  exact sub_eq_zero.mp (hJ (by rw [this, map_zero]))

end S_LinearMap_exists_injective_comp_eq_smul_of_forall_exists_smul_mem_range
end P2MW
export P2MW.S_LinearMap_exists_injective_comp_eq_smul_of_forall_exists_smul_mem_range (solution)
