-- Prove2me | solution 1 for GlobalTheory.relIndex_unfold_semidirect
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:31:16.749451+00:00
-- url     : https://prove2.me/submissions/6b109bbf-4027-417d-8d81-7654e41a0621

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexUnfoldSemidirectProduct
import Theorems.Thm_GlobalTheory_UnfoldSemidirect_mem_map_conj_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Subgroup
open UnfoldSemidirect
namespace GlobalTheory
theorem _root_.solution : ∀ (P M N : Type) [Group P] [Group M] [Group N] (s : M →* P) (π : P →* M) (u : N →* P), (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) → ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N), (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) → ∀ (TM CM : Subgroup M) (TP CP : Subgroup P), CM ≤ TM → (∀ p, p ∈ TP ↔ ∃ t ∈ TM, s t = p) → (∀ p, p ∈ CP ↔ ∃ t ∈ CM, s t = p) → (∀ q : M, TM ⊓ KM.map (MulAut.conj q).toMonoidHom ≤ CM) → ∀ (q : M) (X : N), (TP ⊓ KP.map (MulAut.conj (s q * u X)).toMonoidHom).relIndex CP = (TM ⊓ KM.map (MulAut.conj q).toMonoidHom).relIndex CM * (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM ⊓ KP.comap ((MulAut.conj (u X)⁻¹).toMonoidHom.comp s)).relIndex (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM) := by
  intro P M N _ _ _ s π u hsec hu hker KP KM L hsK hπK huK TM CM TP CP hCT hTP hCP hcond q X
  have hπu : ∀ Y, π (u Y) = 1 := fun Y => (hker _).2 ⟨Y, rfl⟩
  have hsinj : Function.Injective s := fun a b h => by
    have := congrArg π h
    rwa [hsec, hsec] at this
  have key : ∀ r : M, (s q * u X)⁻¹ * s (q * r * q⁻¹) * (s q * u X) = (u X)⁻¹ * s r * u X := by
    intro r; simp only [map_mul, map_inv]; group
  have hπc : ∀ r : M, π ((u X)⁻¹ * s r * u X) = r := by
    intro r; simp [map_mul, map_inv, hπu, hsec]
  have hCP' : CP = CM.map s := by
    ext p; rw [hCP p, Subgroup.mem_map]
  have hH : TP ⊓ KP.map (MulAut.conj (s q * u X)).toMonoidHom
      = ((TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM ⊓
          KP.comap ((MulAut.conj (u X)⁻¹).toMonoidHom.comp s)).map
          (MulAut.conj q).toMonoidHom).map s := by
    ext p
    rw [Subgroup.mem_inf, mem_map_conj_iff, hTP p, Subgroup.mem_map]
    simp only [mem_map_conj_iff, Subgroup.mem_inf, Subgroup.mem_comap, MonoidHom.coe_comp,
      Function.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hk⟩
      have hk' : (u X)⁻¹ * s (q⁻¹ * t * q) * u X ∈ KP := by
        rw [← key]; simpa [mul_assoc] using hk
      refine ⟨t, ⟨⟨?_, ?_⟩, ?_⟩, rfl⟩
      · simpa [mul_assoc] using ht
      · have h1 := hπK _ hk'
        rwa [hπc] at h1
      · simpa using hk'
    · rintro ⟨t, ⟨⟨hr1, hr2⟩, hr3⟩, rfl⟩
      refine ⟨⟨t, by simpa [mul_assoc] using hr1, rfl⟩, ?_⟩
      have := key (q⁻¹ * t * q)
      have e : q * (q⁻¹ * t * q) * q⁻¹ = t := by group
      rw [e] at this
      rw [this]; exact hr3
  have hSq : TM ⊓ KM.map (MulAut.conj q).toMonoidHom
      = (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM).map (MulAut.conj q).toMonoidHom := by
    ext p
    simp only [Subgroup.mem_inf, mem_map_conj_iff, inv_inv]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by simpa [mul_assoc] using h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by simpa [mul_assoc] using h1, h2⟩
  have hle1 : (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM ⊓
          KP.comap ((MulAut.conj (u X)⁻¹).toMonoidHom.comp s)).map (MulAut.conj q).toMonoidHom
        ≤ (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM).map (MulAut.conj q).toMonoidHom :=
    Subgroup.map_mono inf_le_left
  have hle2 : (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM).map (MulAut.conj q).toMonoidHom ≤ CM := by
    rw [← hSq]; exact hcond q
  rw [hH, hCP', Subgroup.relIndex_map_map_of_injective _ _ hsinj,
    ← Subgroup.relIndex_mul_relIndex _ _ _ hle1 hle2,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj q).injective, ← hSq, mul_comm]
end GlobalTheory
