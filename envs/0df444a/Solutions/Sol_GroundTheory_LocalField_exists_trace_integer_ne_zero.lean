-- Prove2me | solution 1 for GroundTheory.LocalField.exists_trace_integer_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:45:18.124491+00:00
-- url     : https://prove2.me/submissions/adefc10d-1d41-41ac-a62d-ecb4ef1d576e

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_ord_zero
import Theorems.Thm_GroundTheory_LocalField_coe_trace_integer
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply


attribute [local simp] GroundTheory.LocalField.coe_normUnits
attribute [local simp] GroundTheory.LocalField.ord_zero

set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing Topology Filter Polynomial
open scoped WithZero nonZeroDivisors
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable {K L}
variable [Algebra.IsSeparable K L]
variable (K L)
namespace GroundTheory.LocalField
theorem _root_.solution : ∃ z : 𝒪[L], Algebra.trace 𝒪[K] 𝒪[L] z ≠ 0 := by
  obtain ⟨w, hw⟩ : ∃ w : L, Algebra.trace K L w ≠ 0 := by
    by_contra h
    refine one_ne_zero ((traceForm_nondegenerate K L).1 1 fun w ↦ ?_)
    simp only [not_exists, not_not] at h
    simpa using h w
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have h1 : valuation L (algebraMap K L (ϖ : K)) < 1 :=
    (Valuation.HasExtension.val_map_lt_one_iff (valuation K) (valuation L) _).mpr
      (valuation_lt_one_of_mem_maximalIdeal (uniformizer_mem_maximalIdeal hϖ))
  have hv0 : valuation L w ≠ 0 := by simpa using hw0
  obtain ⟨m, hm⟩ := exists_pow_lt₀ h1 (Units.mk0 (valuation L w)⁻¹ (inv_ne_zero hv0))
  have hint : algebraMap K L (ϖ : K) ^ m * w ∈ 𝒪[L] := by
    rw [Valuation.mem_integer_iff, map_mul, map_pow]
    calc valuation L (algebraMap K L (ϖ : K)) ^ m * valuation L w
        ≤ (valuation L w)⁻¹ * valuation L w := by
          gcongr
          exact hm.le
      _ = 1 := inv_mul_cancel₀ hv0
  refine ⟨⟨_, hint⟩, fun h ↦ ?_⟩
  have h2 : Algebra.trace K L (algebraMap K L (ϖ : K) ^ m * w) = 0 := by
    have h3 := coe_trace_integer (K := K) (⟨_, hint⟩ : 𝒪[L])
    rw [h, ZeroMemClass.coe_zero] at h3
    exact h3.symm
  rw [← map_pow, ← Algebra.smul_def, map_smul, smul_eq_mul] at h2
  have hϖ0 : (ϖ : K) ≠ 0 := by exact_mod_cast hϖ.ne_zero
  exact mul_ne_zero (pow_ne_zero _ hϖ0) hw h2
end GroundTheory.LocalField
