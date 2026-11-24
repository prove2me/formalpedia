-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CartanU.isCartan_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:54:15.758691+00:00
-- url     : https://prove2.me/submissions/7a5e2c43-0332-4f94-bdd1-88da54bddf5a

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsometricLatticeCongruenceSubgroups
import Theorems.Thm_GlobalTheory_CompanionTheory_CartanU_closure_tor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB CompanionTheory.Rg.Fl
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CartanU
namespace GlobalTheory.CompanionTheory.CartanU
theorem _root_.solution {G : Type} [Group G] (K K₀ : Subgroup G) {d l : ℕ} (T : (Fin l → ℕ) → G)
    (h0 : T 0 = 1) (hadd : ∀ a b, T (a + b) = T a * T b) (c : Fin d → G) (hc : ∀ i, c i ∈ K₀)
    (hcov : ∀ g ∈ K₀, ∃ i, ∃ k ∈ K, g = c i * k)
    (hnorm : ∀ c ∈ K₀, ∀ k, k ∈ K ↔ c * k * c⁻¹ ∈ K)
    (hdec : ∀ g, ∃ k ∈ K₀, ∃ k' ∈ K₀, ∃ r : Fin l → ℕ, Antitone r ∧ g = k * T r * k')
    (hiw : ∀ k ∈ K, ∃ a b : G, k = a * b ∧ ∀ r : Fin l → ℕ, Antitone r →
      T r * a * (T r)⁻¹ ∈ K ∧ (T r)⁻¹ * b * T r ∈ K) :
    IsCartan K d l := by
  have hcl := closure_tor T h0 hadd
  refine ⟨c, fun i => T (ind i), fun i k => hnorm _ (hc i) k, fun i j => ?_, fun g => ?_, ?_⟩
  · show T (ind i) * T (ind j) = T (ind j) * T (ind i)
    rw [← hadd, ← hadd, add_comm]
  · obtain ⟨k, hk, k', hk', r, hr, rfl⟩ := hdec g
    obtain ⟨i, a, ha, rfl⟩ := hcov k hk
    obtain ⟨j, b, hb, rfl⟩ := hcov k' hk'
    refine ⟨i, j, T r, (hcl _).2 ⟨r, hr, rfl⟩, c i * a * (c i)⁻¹, (hnorm _ (hc i) _).1 ha, b, hb, ?_⟩
    group
  · intro x hx y hy k hk
    obtain ⟨r, hr, rfl⟩ := (hcl _).1 hx
    obtain ⟨r', hr', rfl⟩ := (hcl _).1 hy
    obtain ⟨a, b, rfl, hab⟩ := hiw k hk
    exact ⟨_, (hab r hr).1, _, (hab r' hr').2, by group⟩
end GlobalTheory.CompanionTheory.CartanU
