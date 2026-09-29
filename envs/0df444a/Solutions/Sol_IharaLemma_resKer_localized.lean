-- Prove2me | solution 1 for IharaLemma.resKer_localized
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/c0ba6586-a4f9-54e1-8e5c-91b1efeb7c63

import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.LinearAlgebra.Prod
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IharaLemma_resKer_localized

set_option autoImplicit false

theorem solution {R : Type*} [CommRing R] (S : Submonoid R) {V Vk V' Vk' : Type*}
    [AddCommGroup V] [Module R V] [AddCommGroup Vk] [Module R Vk]
    [AddCommGroup V'] [Module R V'] [AddCommGroup Vk'] [Module R Vk']
    (ϖ : R) (redV : V →ₗ[R] Vk)
    (hker : ∀ v, redV v = 0 → ∃ v₁, v = ϖ • v₁)
    (gV : V →ₗ[R] V') [IsLocalizedModule S gV] (gK : Vk →ₗ[R] Vk') [IsLocalizedModule S gK]
    (red' : V' →ₗ[R] Vk') (hsq : ∀ v, red' (gV v) = gK (redV v)) :
    ∀ v' : V', red' v' = 0 → ∃ v₁' : V', v' = ϖ • v₁' := by
  intro v' hv'
  obtain ⟨⟨v, s⟩, hs⟩ := IsLocalizedModule.surj S gV v'
  have hs' : (s : R) • v' = gV v := by rw [← Submonoid.smul_def]; exact hs
  have h0 : gK (redV v) = 0 := by
    rw [← hsq, ← hs', map_smul, hv', smul_zero]
  obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff S gK).mp h0
  rw [Submonoid.smul_def] at ht
  have ht' : redV ((t : R) • v) = 0 := by rw [map_smul, ht]
  obtain ⟨w, hw⟩ := hker _ ht'
  have key : ((t * s : S) : R) • v' = ϖ • gV w := by
    rw [Submonoid.coe_mul, mul_smul, hs', ← map_smul, hw, map_smul]
  obtain ⟨y, hy⟩ :=
    ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units gV (t * s))).2 (gV w)
  rw [Module.algebraMap_end_apply] at hy
  refine ⟨y, IsLocalizedModule.smul_injective gV (t * s) ?_⟩
  show (t * s) • v' = (t * s) • (ϖ • y)
  rw [Submonoid.smul_def, Submonoid.smul_def, key, smul_comm _ ϖ y, hy]

end S_IharaLemma_resKer_localized
end P2MW
export P2MW.S_IharaLemma_resKer_localized (solution)
