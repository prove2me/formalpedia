-- Prove2me | solution 1 for GlobalTheory.PermutationExistence.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:11:15.994999+00:00
-- url     : https://prove2.me/submissions/6c4072e8-ca0d-4611-bf1d-fc5583b64ade

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ImportsRest
import Theorems.Thm_GlobalTheory_PermutationExistence_exists_perm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.PermutationExistence
namespace GlobalTheory.PermutationExistence
theorem _root_.solution {G : Type u_1} {C : Type u_2} [Group G] [NormedField C] [IsUltrametricDist C]
    (act : G →* C ≃+* C) (hn : ∀ (g : G) (y : C), ‖act g y‖ = ‖y‖)
    (H V : Subgroup G) (S : Finset G) (hS : ∀ s ∈ S, s ∈ H)
    (hT : ∀ h ∈ H, ∃! s : G, s ∈ S ∧ s⁻¹ * h ∈ V) (a b : C) (hb : ‖b‖ ≤ (1 : ℝ))
    (hV : ∀ g ∈ V, act g b = b) (ha : ∑ s ∈ S, act s b = a) (c : G → C)
    (hc : ∀ g ∈ H, ∀ h ∈ H, c (g * h) = c g + act g (c h)) (t ε : ℝ) (ht : (0 : ℝ) ≤ t)
    (hε : (0 : ℝ) ≤ ε) (hct : ∀ g ∈ H, ‖c g‖ ≤ t) (hcε : ∀ g ∈ H, g ∈ V → ‖c g‖ ≤ ε) :
    ∃ x : C, ‖x‖ ≤ t ∧ ∀ h ∈ H, ‖a * c h - (act h x - x)‖ ≤ ε := by
  classical
  refine ⟨-∑ s ∈ S, act s b * c s, ?_, ?_⟩
  · rw [norm_neg]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg ht
    intro s hs
    rw [norm_mul, hn]
    calc ‖b‖ * ‖c s‖ ≤ 1 * t := mul_le_mul hb (hct s (hS s hs)) (norm_nonneg _) zero_le_one
      _ = t := one_mul t
  · intro h hh
    obtain ⟨σ, hσ, hsum⟩ := exists_perm (C := C) H V S hS hT h hh
    have hmul : ∀ (g k : G) (y : C), act (g * k) y = act g (act k y) := by
      intro g k y
      rw [map_mul]
      rfl

    have hterm : ∀ s ∈ S, act h (act s b * c s) = act (σ s) b * c (σ s)
        + act (σ s) (b * c ((σ s)⁻¹ * (h * s))) - act (σ s) b * c h := by
      intro s hs
      have hsH := hS s hs
      have hσH := hS (σ s) (hσ s hs).1
      have hvV := (hσ s hs).2
      have hhs : h * s = σ s * ((σ s)⁻¹ * (h * s)) := (mul_inv_cancel_left _ _).symm
      have hvH : (σ s)⁻¹ * (h * s) ∈ H := H.mul_mem (H.inv_mem hσH) (H.mul_mem hh hsH)
      have h1 : act h (act s b) = act (σ s) b := by
        rw [← hmul, hhs, hmul, hV _ hvV]
      have h2 : act h (c s) = c (σ s) + act (σ s) (c ((σ s)⁻¹ * (h * s))) - c h := by
        have e1 := hc h hh s hsH
        have e2 := hc (σ s) hσH _ hvH
        rw [← hhs] at e2
        linear_combination e2 - e1
      rw [map_mul, h1, h2, map_mul (act (σ s)) b (c ((σ s)⁻¹ * (h * s)))]
      ring
    have hsumA : ∑ s ∈ S, act (σ s) b = a := by
      rw [← ha]
      exact hsum (fun g => act g b)
    have hsumT : ∑ s ∈ S, act (σ s) b * c (σ s) = ∑ s ∈ S, act s b * c s :=
      hsum (fun g => act g b * c g)
    have hact : act h (-∑ s ∈ S, act s b * c s) = -(∑ s ∈ S, act s b * c s
        + ∑ s ∈ S, act (σ s) (b * c ((σ s)⁻¹ * (h * s))) - a * c h) := by
      rw [map_neg, map_sum, Finset.sum_congr rfl hterm, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, hsumT, ← Finset.sum_mul, hsumA]
    rw [hact]
    have hE : a * c h - (-(∑ s ∈ S, act s b * c s
        + ∑ s ∈ S, act (σ s) (b * c ((σ s)⁻¹ * (h * s))) - a * c h)
        - -∑ s ∈ S, act s b * c s) = ∑ s ∈ S, act (σ s) (b * c ((σ s)⁻¹ * (h * s))) := by
      ring
    rw [hE]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hε
    intro s hs
    rw [hn, norm_mul]
    have hvH : (σ s)⁻¹ * (h * s) ∈ H :=
      H.mul_mem (H.inv_mem (hS _ (hσ s hs).1)) (H.mul_mem hh (hS s hs))
    calc ‖b‖ * ‖c ((σ s)⁻¹ * (h * s))‖ ≤ 1 * ε :=
          mul_le_mul hb (hcε _ hvH (hσ s hs).2) (norm_nonneg _) zero_le_one
      _ = ε := one_mul ε
end GlobalTheory.PermutationExistence
