-- Prove2me | solution 1 for GroundTheory.LocalField.mem_maximalIdeal_pow_iff_normalizedValuation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:14:23.367298+00:00
-- url     : https://prove2.me/submissions/39da933e-5fba-4a63-86d5-e30e586bdbdf

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_Ramification
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



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable {K L}
variable (K L)
variable {K L}
namespace GroundTheory.LocalField
theorem _root_.solution (n : ℕ) (y : 𝒪[L]) :
    y ∈ 𝓂[L] ^ n ↔ normalizedValuation L (y : L) ≤ WithZero.exp (-(n : ℤ)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  have hv : normalizedValuation L ((ϖ ^ n : 𝒪[L]) : L) = WithZero.exp (-(n : ℤ)) := by
    rw [SubmonoidClass.coe_pow, map_pow, normalizedValuation_uniformizer hϖ, ← WithZero.exp_nsmul]
    simp
  rw [mem_maximalIdeal_pow_iff hϖ, (Valuation.integer.integers (valuation L)).dvd_iff_le, ← hv,
    normalizedValuation_le_iff]
  rfl
end GroundTheory.LocalField
