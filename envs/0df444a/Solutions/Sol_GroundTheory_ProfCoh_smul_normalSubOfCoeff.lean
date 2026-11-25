-- Prove2me | solution 1 for GroundTheory.ProfCoh.smul_normalSubOfCoeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:37:18.476948+00:00
-- url     : https://prove2.me/submissions/cac116f5-be3b-44b9-a771-d9ad451472b5

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsPower
import Definitions.Def_GroundTheory_LocalFields_UnitsGalois
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_Additive
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsLattice
import Theorems.Thm_GroundTheory_ProfCoh_coe_normalSub_smul
import Theorems.Thm_GroundTheory_LocalField_algEquiv_smul_sum
import Theorems.Thm_GroundTheory_LocalField_coe_smul_integerUnits
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
import Theorems.Thm_GroundTheory_ProfCoh_coe_torsNRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_modNRep_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.coe_smul_integerUnits
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply
attribute [local simp] GroundTheory.ProfCoh.coe_torsNRep_apply
attribute [local simp] GroundTheory.ProfCoh.modNRep_mk



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open GroundTheory.LocalField ValuativeRel IsLocalRing
variable {E F : Type*} [Field E] [ValuativeRel E] [Field F] [ValuativeRel F] [Algebra E F]
  [FiniteDimensional E F]
variable [TopologicalSpace E] [IsNonarchimedeanLocalField E] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [ValuativeExtension E F]
attribute [local instance] integerAction
attribute [local instance] normalSubAction
variable {θ : F} (hθ : LinearIndependent E fun σ : F ≃ₐ[E] F ↦ σ θ)
  (hθO : ∀ σ : F ≃ₐ[E] F, σ θ ∈ 𝒪[F])
namespace GroundTheory.ProfCoh
theorem _root_.solution (τ : F ≃ₐ[E] F) (c : (F ≃ₐ[E] F) → 𝒪[E]) :
    τ • normalSubOfCoeff hθO c = normalSubOfCoeff hθO (fun σ ↦ c (τ⁻¹ * σ)) := by
  ext
  rw [coe_normalSub_smul, coe_normalSubOfCoeff, coe_normalSubOfCoeff]
  have := algEquiv_smul_sum (1 : 𝒪[E]) θ τ 0 c
  simpa using this
end GroundTheory.ProfCoh
