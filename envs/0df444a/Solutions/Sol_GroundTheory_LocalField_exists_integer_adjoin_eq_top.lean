-- Prove2me | solution 1 for GroundTheory.LocalField.exists_integer_adjoin_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:58:32.928799+00:00
-- url     : https://prove2.me/submissions/ddca2e21-e581-4e9e-b616-836e2ad7a72c

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Eisenstein
import Definitions.Def_GroundTheory_LocalFields_Monogenic
import Theorems.Thm_GroundTheory_LocalField_residue_aeval_integer
import Theorems.Thm_GroundTheory_LocalField_adjoin_eq_top_of_residue_of_addVal_eq_one
import Theorems.Thm_GroundTheory_LocalField_addVal_eq_one_of_mem_of_notMem_sq
import Theorems.Thm_GroundTheory_LocalField_mem_maximalIdeal_pow_iff_le_addVal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Polynomial IsDiscreteValuationRing IsLocalRing
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable (K L)
namespace GroundTheory.LocalField
theorem _root_.solution : ∃ x : 𝒪[L], Algebra.adjoin 𝒪[K] {x} = ⊤ := by
  classical
  obtain ⟨ξ, hξ⟩ := Field.exists_primitive_element_of_finite_top 𝓀[K] 𝓀[L]
  have hadj : Algebra.adjoin 𝓀[K] {ξ} = ⊤ := IntermediateField.adjoin_eq_top_iff.mp hξ
  have hint : IsIntegral 𝓀[K] ξ := Algebra.IsIntegral.isIntegral ξ
  set P := minpoly 𝓀[K] ξ
  have hsep : P.Separable := PerfectField.separable_of_irreducible (minpoly.irreducible hint)
  obtain ⟨P₀, hP₀⟩ := Polynomial.map_surjective (residue 𝒪[K]) residue_surjective P
  obtain ⟨x₀, hx₀⟩ := residue_surjective ξ

  have hy₀ : aeval x₀ P₀ ∈ IsLocalRing.maximalIdeal 𝒪[L] := by
    rw [← residue_eq_zero_iff, residue_aeval_integer, hP₀, hx₀]
    exact minpoly.aeval _ _
  have hd₀ : IsUnit (aeval x₀ (derivative P₀)) := by
    rw [← not_not (a := IsUnit _), ← mem_nonunits_iff, ← mem_maximalIdeal, ← residue_eq_zero_iff,
      residue_aeval_integer, ← derivative_map, hP₀, hx₀]
    exact hsep.aeval_derivative_ne_zero (minpoly.aeval _ _)

  obtain ⟨x, hxres, hxval⟩ : ∃ x : 𝒪[L], residue 𝒪[L] x = ξ ∧ addVal 𝒪[L] (aeval x P₀) = 1 := by
    by_cases hsq : aeval x₀ P₀ ∈ IsLocalRing.maximalIdeal 𝒪[L] ^ 2
    · obtain ⟨ϖ, hϖ⟩ := exists_irreducible 𝒪[L]
      have hϖ1 : addVal 𝒪[L] ϖ = 1 := addVal_uniformizer hϖ
      refine ⟨x₀ + ϖ, ?_, ?_⟩
      · rw [map_add, hx₀, (residue_eq_zero_iff ϖ).mpr hϖ.not_isUnit, add_zero]
      obtain ⟨k, hk⟩ := binomExpansion (P₀.map (algebraMap 𝒪[K] 𝒪[L])) x₀ ϖ
      rw [eval_map_algebraMap, eval_map_algebraMap, derivative_map, eval_map_algebraMap] at hk
      have hϖm : ϖ ∈ IsLocalRing.maximalIdeal 𝒪[L] := hϖ.not_isUnit
      have hϖsq : ϖ ^ 2 ∈ IsLocalRing.maximalIdeal 𝒪[L] ^ 2 := Ideal.pow_mem_pow hϖm 2
      refine addVal_eq_one_of_mem_of_notMem_sq ?_ ?_
      · rw [hk]
        refine add_mem (add_mem hy₀ (Ideal.mul_mem_left _ _ hϖm)) ?_
        exact Ideal.mul_mem_left _ _ (Ideal.pow_le_self two_ne_zero hϖsq)
      · intro hmem
        have h1 : aeval x₀ (derivative P₀) * ϖ ∈ IsLocalRing.maximalIdeal 𝒪[L] ^ 2 := by
          have : aeval x₀ (derivative P₀) * ϖ =
              aeval (x₀ + ϖ) P₀ - aeval x₀ P₀ - k * ϖ ^ 2 := by rw [hk]; ring
          rw [this]
          exact sub_mem (sub_mem hmem hsq) (Ideal.mul_mem_left _ _ hϖsq)
        obtain ⟨v, hv⟩ := hd₀
        have h2 : ϖ ∈ IsLocalRing.maximalIdeal 𝒪[L] ^ 2 := by
          have := Ideal.mul_mem_left (IsLocalRing.maximalIdeal 𝒪[L] ^ 2) (↑v⁻¹ : 𝒪[L]) h1
          rwa [← hv, ← mul_assoc, Units.inv_mul, one_mul] at this
        rw [mem_maximalIdeal_pow_iff_le_addVal, hϖ1] at h2
        norm_num at h2
    · exact ⟨x₀, hx₀, addVal_eq_one_of_mem_of_notMem_sq hy₀ hsq⟩
  refine ⟨x, adjoin_eq_top_of_residue_of_addVal_eq_one K (π := aeval x P₀) ?_ ?_ hxval⟩
  · rw [hxres]; exact hadj
  · exact aeval_mem_adjoin_singleton 𝒪[K] x
end GroundTheory.LocalField
