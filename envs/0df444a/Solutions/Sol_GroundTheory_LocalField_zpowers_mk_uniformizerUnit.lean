-- Prove2me | solution 1 for GroundTheory.LocalField.zpowers_mk_uniformizerUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:36:41.76641+00:00
-- url     : https://prove2.me/submissions/3b938589-855c-4ebf-bbbf-1555c8da9ce9

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnramifiedDefs
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndex
import Definitions.Def_GroundTheory_LocalFields_UnramifiedNormSurj
import Theorems.Thm_GroundTheory_Global_div_mem_unitFiltration_iff
import Theorems.Thm_GroundTheory_Global_filtrationComplete_unitFiltration
import Theorems.Thm_GroundTheory_Global_filtrationSeparated_unitFiltration
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_ord_mul
import Theorems.Thm_GroundTheory_LocalField_ord_uniformizer
import Theorems.Thm_GroundTheory_LocalField_ord_zero
import Theorems.Thm_GroundTheory_LocalField_ord_zpow
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
attribute [local simp] GroundTheory.LocalField.coe_normUnits
attribute [local simp] GroundTheory.LocalField.ord_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing Filter Polynomial
open GroundTheory.Global (filtrationComplete_unitFiltration filtrationSeparated_unitFiltration
  div_mem_unitFiltration_iff)
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable [IsUnramified K L]
namespace GroundTheory.LocalField
theorem _root_.solution {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    Subgroup.zpowers (QuotientGroup.mk (uniformizerUnit hϖ) : Kˣ ⧸ (normUnits K L).range) = ⊤ := by
  rw [eq_top_iff]
  rintro q -
  induction q using QuotientGroup.induction_on with
  | H x =>
    refine ⟨ord (x : K), ?_⟩
    have hϖ0 : (ϖ : K) ≠ 0 := by exact_mod_cast hϖ.ne_zero
    simp only
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, mem_range_normUnits_iff, Units.val_mul,
      Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, coe_uniformizerUnit,
      ord_mul (inv_ne_zero (zpow_ne_zero _ hϖ0)) x.ne_zero, ← zpow_neg, ord_zpow hϖ0,
      ord_uniformizer hϖ]
    simp
end GroundTheory.LocalField
