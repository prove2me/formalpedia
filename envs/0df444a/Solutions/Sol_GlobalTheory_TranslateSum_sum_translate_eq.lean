-- Prove2me | solution 1 for GlobalTheory.TranslateSum.sum_translate_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:21:30.533845+00:00
-- url     : https://prove2.me/submissions/9107e8df-c301-4df4-8e44-6b1dbf378cee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SumTranslateEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.TranslateSum
namespace GlobalTheory.TranslateSum
theorem _root_.solution {G : Type u_1} {M : Type u_2} [Group G] [AddCommMonoid M]
    (H V : Subgroup G) (S : Finset G) (hS : ∀ s ∈ S, s ∈ H)
    (huniq : ∀ h ∈ H, ∃! s : G, s ∈ S ∧ s⁻¹ * h ∈ V) (f : G → M)
    (hf : ∀ (g v : G), v ∈ H → v ∈ V → f (g * v) = f g) :
    ∀ h ∈ H, ∑ s ∈ S, f (h * s) = ∑ s ∈ S, f s := by
  intro h hh
  have hex : ∀ s ∈ S, ∃ t : G, t ∈ S ∧ t⁻¹ * (h * s) ∈ V := fun s hs =>
    (huniq (h * s) (H.mul_mem hh (hS s hs))).exists
  choose φ hφS hφV using hex
  refine Finset.sum_bij φ hφS ?_ ?_ ?_
  · intro s hs t ht hst
    have h1 : s⁻¹ * t ∈ V := by
      have := V.mul_mem (V.inv_mem (hφV s hs)) (hφV t ht)
      rw [hst] at this
      have e : ((φ t ht)⁻¹ * (h * s))⁻¹ * ((φ t ht)⁻¹ * (h * t)) = s⁻¹ * t := by group
      rwa [e] at this
    have h2 : t⁻¹ * t ∈ V := by
      rw [inv_mul_cancel]; exact V.one_mem
    exact (huniq t (hS t ht)).unique ⟨hs, h1⟩ ⟨ht, h2⟩
  · intro u hu
    obtain ⟨s, hs, hsV⟩ := (huniq (h⁻¹ * u) (H.mul_mem (H.inv_mem hh) (hS u hu))).exists
    refine ⟨s, hs, ?_⟩
    have h1 : u⁻¹ * (h * s) ∈ V := by
      have := V.inv_mem hsV
      have e : (s⁻¹ * (h⁻¹ * u))⁻¹ = u⁻¹ * (h * s) := by group
      rwa [e] at this
    exact (huniq (h * s) (H.mul_mem hh (hS s hs))).unique ⟨hφS s hs, hφV s hs⟩ ⟨hu, h1⟩
  · intro s hs
    have hm : (φ s hs)⁻¹ * (h * s) ∈ H :=
      H.mul_mem (H.inv_mem (hS _ (hφS s hs))) (H.mul_mem hh (hS s hs))
    have := hf (φ s hs) _ hm (hφV s hs)
    rwa [mul_inv_cancel_left] at this
end GlobalTheory.TranslateSum
