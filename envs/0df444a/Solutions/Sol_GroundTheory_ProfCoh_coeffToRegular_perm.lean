-- Prove2me | solution 1 for GroundTheory.ProfCoh.coeffToRegular_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:24:42.540797+00:00
-- url     : https://prove2.me/submissions/4567c310-20fb-4027-aef9-f4fd62bafdc0

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsPower
import Definitions.Def_GroundTheory_LocalFields_UnitsGalois
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_Additive
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsLattice
import Theorems.Thm_GroundTheory_ProfCoh_coeff_coeffToRegular
import Theorems.Thm_GroundTheory_LocalField_coe_smul_integerUnits
import Theorems.Thm_GroundTheory_LocalField_coeff_injective
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
variable {Γ O : Type*} [Fintype Γ] [AddCommGroup O] {p n : ℕ}
  (b : Module.Basis (Fin n) (ZMod p) (ModN O p))
namespace GroundTheory.ProfCoh
theorem _root_.solution [Group Γ] (τ : Γ) (c : Γ → O) :
    coeffToRegular b (fun σ ↦ c (τ⁻¹ * σ)) =
      piRep (Fin n) (Representation.leftRegular (ZMod p) Γ) τ (coeffToRegular b c) := by
  classical
  funext i
  apply MonoidAlgebra.coeff_injective
  ext ρ
  rw [piRep_apply, coeff_coeffToRegular]
  simp only [coeffToRegular, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_sum,
    Representation.ofMulAction_single, smul_eq_mul, MonoidAlgebra.coeff_sum,
    MonoidAlgebra.coeff_single, Finset.sum_apply', Finsupp.single_apply]
  rw [Finset.sum_eq_single (τ⁻¹ * ρ)]
  · simp
  · intro σ _ hσ
    rw [if_neg]
    intro h
    apply hσ
    rw [← h]
    group
  · simp
end GroundTheory.ProfCoh
