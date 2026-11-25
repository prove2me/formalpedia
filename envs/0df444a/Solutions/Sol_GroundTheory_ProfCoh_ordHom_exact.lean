-- Prove2me | solution 1 for GroundTheory.ProfCoh.ordHom_exact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:35:10.50508+00:00
-- url     : https://prove2.me/submissions/959bb229-a981-470e-87db-da49cbf6460a

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsLattice
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_ModNEquivOfSurjectiveApplyModNRep
import Theorems.Thm_GroundTheory_ProfCoh_ordHom_apply
import Theorems.Thm_GroundTheory_LocalField_coe_smul_integerUnits
import Theorems.Thm_GroundTheory_LocalField_mem_range_unitsIncl_iff
import Theorems.Thm_GroundTheory_LocalField_normalizedValuation_eq_exp_ord
import Theorems.Thm_GroundTheory_LocalField_ord_unit
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
universe u
open GroundTheory.LocalField ValuativeRel IsLocalRing
variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {F}
namespace GroundTheory.ProfCoh
theorem _root_.solution : Function.Exact (unitsIncl F).toAdditive (ordHom F) := by
  intro x
  rw [ordHom_apply]
  constructor
  · intro h
    have h0 : ord ((x.toMul : Fˣ) : F) = 0 := congrArg ULift.down h
    have h1 : normalizedValuation F ((x.toMul : Fˣ) : F) = 1 := by
      rw [normalizedValuation_eq_exp_ord x.toMul.ne_zero, h0, neg_zero, WithZero.exp_zero]
    obtain ⟨u, hu⟩ := mem_range_unitsIncl_iff.mpr h1
    exact ⟨Additive.ofMul u, by simp [hu]⟩
  · rintro ⟨u, rfl⟩
    apply ULift.ext
    simp [ord_unit]
end GroundTheory.ProfCoh
