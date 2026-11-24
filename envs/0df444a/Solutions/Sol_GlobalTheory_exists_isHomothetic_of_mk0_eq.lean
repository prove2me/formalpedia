-- Prove2me | solution 1 for GlobalTheory.exists_isHomothetic_of_mk0_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:03:21.890941+00:00
-- url     : https://prove2.me/submissions/ecb02eeb-f07d-4024-85ca-65b978afb877

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SumLogNormEmbeddingEqFinrankMulLogAbsNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeCmEqIdealAndCovolume
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeDeterminedByInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MeanLogCovolumeEqMeanClassGroup
import Theorems.Thm_GlobalTheory_exists_mul_mem_iff_of_mk0_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex NumberField
open scoped nonZeroDivisors Real UpperHalfPlane
noncomputable section
open GlobalTheory
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory
theorem _root_.solution (σ : K →+* ℂ) (𝔞 𝔟 𝔡 : (Ideal (𝓞 K))⁰)
    (h : ClassGroup.mk0 𝔡 * ClassGroup.mk0 𝔟 = ClassGroup.mk0 𝔞) {L L' P : PeriodPair}
    {c β : ℂ} (hc : c ≠ 0) (hβ : β ≠ 0)
    (hL : ∀ z, z ∈ L.lattice ↔ ∃ a ∈ (𝔞 : Ideal (𝓞 K)), z = c * σ (a : K))
    (hL' : ∀ z, z ∈ L'.lattice ↔ ∀ y ∈ (𝔟 : Ideal (𝓞 K)), β⁻¹ * σ (y : K) * z ∈ L.lattice)
    (hP : ∀ z, z ∈ P.lattice ↔ ∃ d ∈ (𝔡 : Ideal (𝓞 K)), z = σ (d : K)) :
    ∃ κ : ℂ, IsHomothetic κ P L' := by
  obtain ⟨u, hu, H⟩ := exists_mul_mem_iff_of_mk0_eq 𝔞 𝔟 𝔡 h
  have hu' : σ u ≠ 0 := (map_ne_zero σ).2 hu
  refine ⟨β * c * σ u, fun z => ?_⟩
  have e : ∀ (y : 𝓞 K) (t : K), β⁻¹ * σ (y : K) * (β * c * σ u * σ t) = c * σ (u * t * y) := by
    intro y t
    rw [map_mul, map_mul]
    field_simp
  rw [hL', hP]
  constructor
  · intro hz
    obtain ⟨t, rfl⟩ : ∃ t : K, z = σ t := by
      obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (nonZeroDivisors.coe_ne_zero 𝔟)
      obtain ⟨a, -, ha⟩ := (hL _).1 (hz y hy)
      have hy1 : σ (y : K) ≠ 0 := by
        rw [map_ne_zero]; exact_mod_cast hy0
      refine ⟨a / (u * y), ?_⟩
      rw [map_div₀, map_mul]
      field_simp
      field_simp at ha
      linear_combination ha
    obtain ⟨d, hd, rfl⟩ := (H t).1 fun b hb => by
      obtain ⟨a, ha, e'⟩ := (hL _).1 (hz b hb)
      rw [e] at e'
      exact ⟨a, ha, σ.injective (mul_left_cancel₀ hc e')⟩
    exact ⟨d, hd, rfl⟩
  · rintro ⟨d, hd, rfl⟩ y hy
    obtain ⟨a, ha, e'⟩ := (H d).2 ⟨d, hd, rfl⟩ y hy
    rw [e, e']
    exact (hL _).2 ⟨a, ha, rfl⟩
end GlobalTheory
