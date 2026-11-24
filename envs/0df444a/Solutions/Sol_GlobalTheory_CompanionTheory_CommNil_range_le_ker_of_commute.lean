-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CommNil.range_le_ker_of_commute
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:24:23.841796+00:00
-- url     : https://prove2.me/submissions/54d231cb-b1e4-499a-a487-a1de17050c41

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_FinrankRangePowConvex
import Theorems.Thm_GlobalTheory_CompanionTheory_CommNil_range_pow_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CommNil
open Module
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.CommNil
theorem _root_.solution (a b : Module.End ℂ V) (hab : Commute b a) (ha : IsNilpotent a)
    (x : ℕ) (Y : Submodule ℂ V) (hY : Y ⊔ LinearMap.range (a ^ (x + 1)) = LinearMap.range (a ^ x))
    (hb : Y ≤ LinearMap.ker b) : LinearMap.range (a ^ x) ≤ LinearMap.ker b := by
  have step : ∀ v ∈ LinearMap.range (a ^ x), ∃ u ∈ LinearMap.range (a ^ x), b v = a (b u) := by
    intro v hv
    rw [← hY] at hv
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
    rw [range_pow_succ] at hz
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.1 hz
    refine ⟨u, hu, ?_⟩
    have hba := LinearMap.congr_fun hab.eq u
    rw [Module.End.mul_apply, Module.End.mul_apply] at hba
    rw [map_add, LinearMap.mem_ker.1 (hb hy), zero_add, hba]
  have key : ∀ k : ℕ, ∀ v ∈ LinearMap.range (a ^ x), ∃ u ∈ LinearMap.range (a ^ x),
      b v = (a ^ k) (b u) := by
    intro k
    induction k with
    | zero => exact fun v hv => ⟨v, hv, by simp⟩
    | succ k ih =>
      intro v hv
      obtain ⟨u, hu, h1⟩ := ih v hv
      obtain ⟨u', hu', h2⟩ := step u hu
      exact ⟨u', hu', by rw [h1, h2, pow_succ, Module.End.mul_apply]⟩
  obtain ⟨N, hN⟩ := ha
  intro v hv
  obtain ⟨u, _, hu⟩ := key N v hv
  rw [LinearMap.mem_ker, hu, hN, LinearMap.zero_apply]
end GlobalTheory.CompanionTheory.CommNil
