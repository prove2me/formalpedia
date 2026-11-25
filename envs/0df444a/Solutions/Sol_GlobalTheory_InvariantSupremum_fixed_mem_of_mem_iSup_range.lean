-- Prove2me | solution 1 for GlobalTheory.InvariantSupremum.fixed_mem_of_mem_iSup_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:53:59.851706+00:00
-- url     : https://prove2.me/submissions/b2117ff7-f5db-46e4-921c-c64b53e7d11d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqBotOrEqTopOfInvariant
import Theorems.Thm_GlobalTheory_InvariantSupremum_eq_bot_or_eq_top_of_invariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.InvariantSupremum
namespace GlobalTheory.InvariantSupremum
theorem _root_.solution {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {ι : Type} (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) (hσ : Representation.IsIrreducible σ) (f : ι → W →ₗ[ℂ] V)
    (hf : ∀ (i : ι) (g : G) (u : W), f i (σ g u) = ρ g (f i u)) (K : Set G)
    (Z : Submodule ℂ V) (hZ : ∀ (i : ι) (v : W), (∀ k ∈ K, σ k v = v) → f i v ∈ Z)
    (_hfix : ∀ z ∈ Z, ∀ k ∈ K, ρ k z = z) (φ : V) (hφ : ∀ k ∈ K, ρ k φ = φ)
    (hmem : φ ∈ ⨆ i : ι, LinearMap.range (f i)) : φ ∈ Z := by
  classical
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp hmem
  clear hmem

  have inv : ∀ (t : Finset ι) (g : G), ∀ z ∈ ⨆ i ∈ t, LinearMap.range (f i),
      ρ g z ∈ ⨆ i ∈ t, LinearMap.range (f i) := by
    intro t g z hz
    have hle : (⨆ i ∈ t, LinearMap.range (f i)) ≤
        (⨆ i ∈ t, LinearMap.range (f i)).comap (ρ g) := by
      refine iSup₂_le fun i hi => ?_
      rintro _ ⟨w, rfl⟩
      rw [Submodule.mem_comap, ← hf i g w]
      exact (le_iSup₂ (f := fun i (_ : i ∈ t) => LinearMap.range (f i)) i hi)
        (LinearMap.mem_range_self _ _)
    exact hle hz
  induction s using Finset.induction_on generalizing φ with
  | empty =>
    simp only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot] at hs
    rw [hs]
    exact Z.zero_mem
  | @insert j s hj ih =>
    rw [Finset.iSup_insert, Submodule.mem_sup] at hs
    obtain ⟨y, ⟨u, rfl⟩, z, hz, rfl⟩ := hs

    rcases eq_bot_or_eq_top_of_invariant σ hσ ((⨆ i ∈ s, LinearMap.range (f i)).comap (f j)) (by
        intro g w hw
        rw [Submodule.mem_comap] at hw ⊢
        rw [hf]
        exact inv s g _ hw) with hN | hN
    ·
      have hu : ∀ k ∈ K, σ k u = u := by
        intro k hk
        have e : ρ k (f j u) - f j u = z - ρ k z := by
          rw [sub_eq_sub_iff_add_eq_add, ← map_add, hφ k hk, add_comm]
        have h1 : σ k u - u ∈ (⨆ i ∈ s, LinearMap.range (f i)).comap (f j) := by
          rw [Submodule.mem_comap, map_sub, hf, e]
          exact Submodule.sub_mem _ hz (inv s k z hz)
        rw [hN, Submodule.mem_bot, sub_eq_zero] at h1
        exact h1
      have hzfix : ∀ k ∈ K, ρ k z = z := by
        intro k hk
        have h2 := hφ k hk
        rw [map_add, ← hf, hu k hk] at h2
        exact add_left_cancel h2
      exact Z.add_mem (hZ j u hu) (ih z hzfix hz)
    ·
      have hu : f j u ∈ ⨆ i ∈ s, LinearMap.range (f i) := by
        have h3 : u ∈ (⨆ i ∈ s, LinearMap.range (f i)).comap (f j) := by
          rw [hN]
          trivial
        exact h3
      exact ih _ hφ (Submodule.add_mem _ hu hz)
end GlobalTheory.InvariantSupremum
