-- Prove2me | solution 1 for GlobalTheory.SplitWeil.exists_hasConductor_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:25.442081+00:00
-- url     : https://prove2.me/submissions/fc631abc-2b4a-469f-9705-3af1391e0f0f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Theorems.Thm_GlobalTheory_SplitWeil_exists_cball_addChar_eq_one
import Theorems.Thm_GlobalTheory_SplitWeil_mem_cball_uniformiser


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitWeil
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.SplitWeil
theorem _root_.solution (ψ : AddChar k Circle) (hψ : Continuous ψ) (h1 : ψ ≠ 1) :
    ∃ c : kˣ, HasConductor ψ c := by
  classical
  obtain ⟨s, hs⟩ := exists_cball_addChar_eq_one ψ hψ
  obtain ⟨y₀, hy₀⟩ : ∃ y, ψ y ≠ 1 := by
    by_contra h
    push Not at h
    exact h1 (by ext y; simp [h y])
  have hy0 : y₀ ≠ 0 := by
    rintro rfl
    exact hy₀ (AddChar.map_zero_eq_one ψ)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  have h0 : (ϖ : k) ≠ 0 := by simpa using hϖ.ne_zero
  have hlt : ∀ y : 𝒪[k], y ∈ 𝓂[k] ↔ valuation k (y : k) < 1 := fun y => by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one
  have hϖ1 : valuation k (ϖ : k) < 1 := (hlt ϖ).mp hϖ.not_isUnit
  have hex : ∃ n : ℕ, ∀ y, valuation k y ≤ valuation k (y₀ * (ϖ : k) ^ n) → ψ y = 1 := by
    obtain ⟨n, hn⟩ := exists_pow_lt₀ hϖ1
      (Units.mk0 (valuation k (y₀⁻¹ * s)) (by simp [hy0]))
    refine ⟨n, fun y hy => hs y (show valuation k y ≤ valuation k (s : k) from hy.trans ?_)⟩
    rw [Units.val_mk0, map_mul, map_inv₀, lt_inv_mul_iff₀ (by simp [zero_lt_iff, hy0])] at hn
    rw [map_mul, map_pow]
    exact hn.le
  have hspec := Nat.find_spec hex
  have hne : Nat.find hex ≠ 0 := by
    intro h
    rw [h] at hspec
    exact hy₀ (hspec y₀ (by simp))
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hne
  have hmin := Nat.find_min hex (m := m) (by omega)
  rw [hm] at hspec
  refine ⟨Units.mk0 (y₀ * (ϖ : k) ^ (m + 1)) (mul_ne_zero hy0 (pow_ne_zero _ h0)), fun x => ⟨fun h => ?_,
    fun h y hy => hspec y (hy.trans h)⟩⟩
  by_contra hx
  rw [Units.val_mk0, not_le] at hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have hxp : 0 < valuation k x := by simp [zero_lt_iff, hx0]
  have hxi : valuation k (x⁻¹ * (y₀ * (ϖ : k) ^ (m + 1))) < 1 := by
    rw [map_mul, map_inv₀, inv_mul_lt_iff₀ hxp, mul_one]
    exact hx
  have h2 : valuation k (x⁻¹ * (y₀ * (ϖ : k) ^ (m + 1))) ≤ valuation k (ϖ : k) :=
    (mem_cball_uniformiser hϖ (x := Units.mk0 _ h0) rfl
      ⟨_, (Valuation.mem_integer_iff _ _).mpr hxi.le⟩).mpr ((hlt _).mpr hxi)
  rw [map_mul, map_inv₀, inv_mul_le_iff₀ hxp, pow_succ, ← mul_assoc, map_mul,
    mul_le_mul_iff_left₀ (by simp [zero_lt_iff, h0])] at h2
  exact hmin fun y hy => h y (hy.trans h2)
end GlobalTheory.SplitWeil
