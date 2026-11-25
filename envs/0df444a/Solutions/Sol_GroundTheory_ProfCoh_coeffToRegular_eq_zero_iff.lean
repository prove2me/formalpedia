-- Prove2me | solution 1 for GroundTheory.ProfCoh.coeffToRegular_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:24:41.78864+00:00
-- url     : https://prove2.me/submissions/bb4129b4-618d-4e6a-a638-a34e30138f1d

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
theorem _root_.solution (c : Γ → O) :
    coeffToRegular b c = 0 ↔ c ∈ LinearMap.range (LinearMap.lsmul ℤ (Γ → O) p) := by
  rw [mem_range_lsmul_iff]
  constructor
  · intro h
    have h0 : ∀ τ, (Submodule.Quotient.mk (c τ) : ModN O p) = 0 := by
      intro τ
      apply b.repr.injective
      ext i
      have := congrArg (fun x ↦ (x i).coeff τ) h
      simpa [coeff_coeffToRegular] using this
    choose y hy using fun τ ↦ (mem_range_lsmul_iff).mp ((Submodule.Quotient.mk_eq_zero _).mp (h0 τ))
    exact ⟨y, funext fun τ ↦ by simpa using hy τ⟩
  · rintro ⟨y, rfl⟩
    funext i
    apply MonoidAlgebra.coeff_injective
    ext τ
    rw [coeff_coeffToRegular]
    simp
end GroundTheory.ProfCoh
