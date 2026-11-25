-- Prove2me | solution 1 for GroundTheory.Global.finite_quotient_range_valuationVector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:32:10.124074+00:00
-- url     : https://prove2.me/submissions/10beb23d-6af1-42e8-b324-bd6f1372b13d

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SUnits
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Lattice
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsExact
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsPerm
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsRep
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_UnitsHerbrandValue
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnits
import Theorems.Thm_GroundTheory_Global_SUnit_valuationVector_comp_placeUnitsMap
import Theorems.Thm_GroundTheory_Global_SemiLocal_tensorHomeomorph_apply
import Theorems.Thm_GroundTheory_Global_coeff_permOfFun
import Theorems.Thm_GroundTheory_Global_cycSub_apply
import Theorems.Thm_GroundTheory_Global_finite_quotient_of_smul_mem
import Theorems.Thm_GroundTheory_Global_normHom_apply
import Theorems.Thm_GroundTheory_Global_piRep_apply
import Theorems.Thm_GroundTheory_GroupCoh_restrictEnd_apply
import Theorems.Thm_P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.SemiLocal.tensorHomeomorph_apply
attribute [local simp] GroundTheory.Global.coeff_permOfFun
attribute [local simp] GroundTheory.Global.cycSub_apply
attribute [local simp] GroundTheory.Global.normHom_apply
attribute [local simp] GroundTheory.Global.piRep_apply
attribute [local simp] GroundTheory.GroupCoh.restrictEnd_apply
attribute [local simp] P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7



set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain MulAction Module
noncomputable section
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]
variable (S : Set (HeightOneSpectrum (𝓞 L))) [Finite S]
omit [IsGalois K L]
namespace GroundTheory.Global
theorem _root_.solution :
    Finite ((S → ℤ) ⧸ (SUnit.valuationVector (K := L) S).toAddMonoidHom.range) := by
  have hn : (-(classNumber L : ℤ)) ≠ 0 := by
    simpa using classNumber_ne_zero L
  refine finite_quotient_of_smul_mem _ hn fun y => ⟨SUnit.placeUnitsMap S y, ?_⟩
  change (SUnit.valuationVector S ∘ₗ SUnit.placeUnitsMap S) y = _
  rw [SUnit.valuationVector_comp_placeUnitsMap]
  rfl
end GroundTheory.Global
