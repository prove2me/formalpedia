-- Prove2me | solution 1 for GlobalTheory.Cyc.FontW.avg_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:25:12.193048+00:00
-- url     : https://prove2.me/submissions/cba99398-ec0a-43ca-9018-b4b20bc2e3cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TensorRight
import Theorems.Thm_GlobalTheory_Cyc_FontW_Dv_map
import Theorems.Thm_GlobalTheory_Cyc_FontW_Dv_smul
import Theorems.Thm_GlobalTheory_Cyc_FontW_sum_translate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.FontW
variable {G A M : Type*} [Group G] [CommRing A] [AddCommGroup M] [Module A M] (l : ℕ)
  (𝓕 : Filter G) (a : G → A → A) (ρ : G → M →+ M)
namespace GlobalTheory.Cyc.FontW
theorem _root_.solution (amul : ∀ g h β, a (g * h) β = a g (a h β))
    (ρmul : ∀ g h x, ρ (g * h) x = ρ g (ρ h x))
    (semi : ∀ g β x, ρ g (β • x) = a g β • ρ g x)
    (htr : ∀ W ∈ 𝓕, ∃ N : Subgroup G, N.Normal ∧ (N : Set G) ∈ 𝓕 ∧ (N : Set G) ⊆ W ∧
      ∃ S : Finset G, (∀ h, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ N) ∧
        ∃ β, (∀ n ∈ N, a n β = β) ∧ ∑ s ∈ S, a s β = 1)
    (c : G → M) (hc : ∀ g h, c (g * h) = c g + ρ g (c h))
    (hcont : ∀ r, {g | c g ∈ Dv l r M} ∈ 𝓕) (k : ℕ) (hk : ∀ g, c g ∈ Dv l k M) :
    ∃ b ∈ Dv l k M, (∀ r, {g | c g - (ρ g b - b) ∈ Dv l r M} ∈ 𝓕) ∧
      ∀ g, c g - (ρ g b - b) ∈ Dv l (k + 1) M := by
  obtain ⟨N, hN, hNF, hNW, S, hS, β, hβ, hsum⟩ := htr _ (hcont (k + 1))
  have hβ' : ∀ g, ∀ n ∈ N, a (g * n) β = a g β := fun g n hn => by rw [amul, hβ n hn]
  have hρ : ∀ σ, ρ σ (∑ s ∈ S, a s β • c s) = ∑ s ∈ S, a (σ * s) β • ρ σ (c s) := by
    intro σ
    rw [map_sum]
    exact Finset.sum_congr rfl fun s _ => by rw [semi, amul]
  refine ⟨-∑ s ∈ S, a s β • c s, neg_mem (sum_mem fun s _ => Dv_smul _ (hk s)), fun r => ?_,
    fun σ => ?_⟩
  · obtain ⟨N', hN', hNF', hNW', -⟩ := htr _ (hcont r)
    filter_upwards [hNF, hNF'] with n hn hn'
    refine sub_mem (hNW' hn') ?_
    rw [map_neg, hρ, neg_sub_neg, ← Finset.sum_sub_distrib]
    refine sum_mem fun s _ => ?_
    have h1 : n * s = s * (s⁻¹ * n * s) := by group
    have h2 : a (n * s) β = a s β := by
      rw [h1]; exact hβ' _ _ (by simpa using hN.conj_mem n hn s⁻¹)
    rw [h2, ← smul_sub]
    refine Dv_smul _ ?_
    have h3 : c s - ρ n (c s) = c n - ρ s (c (s⁻¹ * n * s)) := by
      have h4 := hc n s
      rw [h1, hc] at h4
      rw [sub_eq_sub_iff_add_eq_add, h4]
    rw [h3]
    exact sub_mem (hNW' hn') (Dv_map _ (hNW' (by simpa using hN'.conj_mem n hn' s⁻¹)))
  · have h1 : ∑ s ∈ S, a (σ * s) β = 1 := by
      rw [sum_translate N S hS (fun g => a g β) hβ' σ, hsum]
    have h2 : c σ - (ρ σ (-∑ s ∈ S, a s β • c s) - -∑ s ∈ S, a s β • c s) =
        ∑ s ∈ S, a (σ * s) β • c (σ * s) - ∑ s ∈ S, a s β • c s := by
      rw [map_neg, hρ]
      simp only [hc, smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, h1, one_smul]
      abel
    rw [h2, ← QuotientAddGroup.eq_iff_sub_mem]
    have h3 := sum_translate N S hS
      (fun g => QuotientAddGroup.mk' (Dv l (k + 1) M) (a g β • c g)) (fun g n hn => by
        rw [hβ' g n hn]
        refine QuotientAddGroup.eq_iff_sub_mem.2 ?_
        rw [hc, smul_add, add_sub_cancel_left]
        exact Dv_smul _ (Dv_map _ (hNW hn))) σ
    rw [← map_sum, ← map_sum] at h3
    exact h3
end GlobalTheory.Cyc.FontW
