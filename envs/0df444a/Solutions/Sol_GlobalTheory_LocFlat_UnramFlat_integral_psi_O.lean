-- Prove2me | solution 1 for GlobalTheory.LocFlat.UnramFlat.integral_psi_O
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:30:33.890711+00:00
-- url     : https://prove2.me/submissions/1f7b533b-502f-43f9-a5ad-c0f9744a77cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEmbXMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatContrIntIndicator
import Theorems.Thm_GlobalTheory_RootEx_Unram_mem_of_psi
import Theorems.Thm_GlobalTheory_RootEx_Unram_psi_eq_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option linter.unusedSectionVars false
noncomputable section
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.UnramFlat
open GlobalTheory.RootEx.Unram GlobalTheory.LocFlat
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
open Classical
namespace GlobalTheory.LocFlat.UnramFlat
theorem _root_.solution {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ν : Measure k} (hν : IsUnitVol ν) (a : k) :
    ∫ t, (if t ∈ 𝒪[k] then (1 : ℂ) else 0) * (ψ (-1 * (a * t)) : ℂ) ∂ν = if a ∈ 𝒪[k] then 1 else 0 := by
  haveI := hν.1
  have hO : MeasurableSet (𝒪[k] : Set k) := (Valuation.isOpen_integer (v := valuation k)).measurableSet
  by_cases ha : a ∈ 𝒪[k]
  · rw [if_pos ha]
    have : (fun t => (if t ∈ 𝒪[k] then (1 : ℂ) else 0) * (ψ (-1 * (a * t)) : ℂ)) =
        Set.indicator (𝒪[k] : Set k) (fun _ => 1) := by
      funext t
      by_cases ht : t ∈ 𝒪[k]
      · rw [if_pos ht, Set.indicator_of_mem (show t ∈ (𝒪[k] : Set k) from ht),
          psi_eq_one hψ (by simpa using neg_mem (mul_mem ha ht))]
        simp
      · rw [if_neg ht, Set.indicator_of_notMem (show t ∉ (𝒪[k] : Set k) from ht), zero_mul]
    rw [this, integral_indicator_const _ hO]
    simp [Measure.real, hν.2]
  · rw [if_neg ha]
    obtain ⟨t₀, ht₀, hne⟩ : ∃ t₀ ∈ 𝒪[k], ψ (t₀ * (-a)) ≠ 1 := by
      by_contra h
      push_neg at h
      exact ha (by simpa using neg_mem (mem_of_psi hψ h))
    set F : k → ℂ := fun t => (if t ∈ 𝒪[k] then (1 : ℂ) else 0) * (ψ (-1 * (a * t)) : ℂ) with hF
    have hFt : ∀ t, F (t₀ + t) = (ψ (t₀ * (-a)) : ℂ) * F t := by
      intro t
      simp only [hF]
      have hm : t₀ + t ∈ 𝒪[k] ↔ t ∈ 𝒪[k] :=
        ⟨fun h => by simpa using sub_mem h ht₀, fun h => add_mem ht₀ h⟩
      rw [if_congr hm rfl rfl, show -1 * (a * (t₀ + t)) = t₀ * (-a) + -1 * (a * t) by ring,
        AddChar.map_add_eq_mul, Circle.coe_mul]
      ring
    have hI := integral_add_left_eq_self (μ := ν) F t₀
    simp_rw [hFt] at hI
    rw [integral_const_mul] at hI
    have hne' : (ψ (t₀ * (-a)) : ℂ) ≠ 1 := fun h => hne (Circle.coe_inj.1 (by simpa using h))
    have h3 : ((ψ (t₀ * (-a)) : ℂ) - 1) * ∫ t, F t ∂ν = 0 := by rw [sub_mul, hI]; ring
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd (sub_eq_zero.1 h) hne'
    · exact h
end GlobalTheory.LocFlat.UnramFlat
