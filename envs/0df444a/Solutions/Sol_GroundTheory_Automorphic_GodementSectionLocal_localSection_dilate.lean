-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementSectionLocal.localSection_dilate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:41:59.369196+00:00
-- url     : https://prove2.me/submissions/9a5ef656-58a3-4866-bacd-7e88a1548a18

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GodementSectionLocal
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_modPow_units_eq_zpow
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_localSection_smul_arg
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_ord_unifPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Filter Topology
open scoped NNReal ValuativeRel
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.GodementSectionLocal
open GroundTheory.LocalField
noncomputable section
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [MeasurableSpace F] [BorelSpace F]
namespace GroundTheory.Automorphic.GodementSectionLocal
theorem _root_.solution (χ₁ χ₂ : Fˣ →* ℂˣ) (s : ℂ) (Ψ : (Fin 2 → F) → ℂ) (k : ℤ) :
    localSection χ₁ χ₂ s (fun x ↦ Ψ (((unifPow (-k) : Fˣ) : F) • x)) =
      ((((χ₁ * χ₂⁻¹) (unifUnit F) : ℂˣ) : ℂ) ^ k * ((residueCard F : ℂ) ^ (-(2 * s))) ^ k) •
        localSection χ₁ χ₂ s Ψ := by
  rw [localSection_smul_arg]
  congr 1
  have h1 : ((((χ₁ * χ₂⁻¹) (unifPow (-k)))⁻¹ : ℂˣ) : ℂ) =
      (((χ₁ * χ₂⁻¹) (unifUnit F) : ℂˣ) : ℂ) ^ k := by
    rw [unifPow, map_zpow, ← _root_.zpow_neg, neg_neg, Units.val_zpow_eq_zpow_val]
  have h2 : modPow ((unifPow (-k) : Fˣ) : F) (-(2 * s)) =
      ((residueCard F : ℂ) ^ (-(2 * s))) ^ k := by
    rw [modPow_units_eq_zpow, ord_unifPow, neg_neg, Complex.cpow_neg, _root_.inv_zpow']
  rw [h1, h2]
end GroundTheory.Automorphic.GodementSectionLocal
