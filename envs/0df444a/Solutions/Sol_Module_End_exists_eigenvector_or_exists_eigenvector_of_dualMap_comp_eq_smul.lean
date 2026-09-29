-- Prove2me | solution 1 for Module.End.exists_eigenvector_or_exists_eigenvector_of_dualMap_comp_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/45e8a416-5910-545f-82f9-05f3e9dc6531

import Mathlib
import Theorems.Thm_Module_End_exists_ne_zero_forall_apply_eq_smul_of_forall_sub_smul_mem
import Theorems.Thm_Module_End_exists_ne_zero_forall_apply_eq_smul_iff_exists_ne_zero_forall_dualMap_apply_eq_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_End_exists_eigenvector_or_exists_eigenvector_of_dualMap_comp_eq_smul

set_option autoImplicit false

theorem solution
    {K : Type*} [Field K]
    {L S Ω' : Type*} [AddCommGroup L] [Module K L] [AddCommGroup S] [Module K S] [AddCommGroup Ω'] [Module K Ω']
    [FiniteDimensional K L] [FiniteDimensional K Ω']
    {ι : Type*}
    (TL : ι → Module.End K L) (hTL : ∀ i j, Commute (TL i) (TL j))
    (TS : ι → Module.End K S)
    (TΩ : ι → Module.End K Ω') (hTΩ : ∀ i j, Commute (TΩ i) (TΩ j))
    (res : L →ₗ[K] S) (hres : ∀ i, res ∘ₗ TL i = TS i ∘ₗ res)
    (Θ : S →ₗ[K] Module.Dual K Ω') (hexact : ∀ v : S, Θ v = 0 ↔ v ∈ LinearMap.range res)
    (c : ι → K) (hc : ∀ i, c i ≠ 0)
    (hΘ : ∀ (i : ι) (v : S), Θ (TS i v) = c i • (TΩ i).dualMap (Θ v))
    (lam : ι → K) (v : S) (hv0 : v ≠ 0) (hv : ∀ i, TS i v = lam i • v) :
    (∃ G : L, G ≠ 0 ∧ ∀ i, TL i G = lam i • G) ∨
    (∃ ω : Ω', ω ≠ 0 ∧ ∀ i, TΩ i ω = ((c i)⁻¹ * lam i) • ω) := by
  by_cases hΘv : Θ v = 0
  ·
    left
    obtain ⟨v', rfl⟩ := (hexact v).mp hΘv
    have hW : ∀ i, ∀ w ∈ LinearMap.ker res, TL i w ∈ LinearMap.ker res := by
      intro i w hw
      rw [LinearMap.mem_ker] at hw ⊢
      have := LinearMap.congr_fun (hres i) w
      simp only [LinearMap.coe_comp, Function.comp_apply] at this
      rw [this, hw, map_zero]
    have hv' : v' ∉ LinearMap.ker res := fun h => hv0 (LinearMap.mem_ker.mp h)
    have heig : ∀ i, TL i v' - lam i • v' ∈ LinearMap.ker res := by
      intro i
      rw [LinearMap.mem_ker, map_sub, map_smul]
      have := LinearMap.congr_fun (hres i) v'
      simp only [LinearMap.coe_comp, Function.comp_apply] at this
      rw [this, hv i, sub_self]
    exact Module.End.exists_ne_zero_forall_apply_eq_smul_of_forall_sub_smul_mem TL hTL (LinearMap.ker res) hW lam v' hv' heig
  ·
    right
    have hdual : ∀ i, (TΩ i).dualMap (Θ v) = ((c i)⁻¹ * lam i) • Θ v := by
      intro i
      have h := hΘ i v
      rw [hv i, map_smul] at h

      have := congrArg (fun φ => (c i)⁻¹ • φ) h
      simp only [smul_smul, inv_mul_cancel₀ (hc i), one_smul] at this
      rw [← this, mul_comm]
    exact (Module.End.exists_ne_zero_forall_apply_eq_smul_iff_exists_ne_zero_forall_dualMap_apply_eq_smul TΩ hTΩ
      (fun i => (c i)⁻¹ * lam i)).mpr ⟨Θ v, hΘv, hdual⟩

end S_Module_End_exists_eigenvector_or_exists_eigenvector_of_dualMap_comp_eq_smul
end P2MW
export P2MW.S_Module_End_exists_eigenvector_or_exists_eigenvector_of_dualMap_comp_eq_smul (solution)
