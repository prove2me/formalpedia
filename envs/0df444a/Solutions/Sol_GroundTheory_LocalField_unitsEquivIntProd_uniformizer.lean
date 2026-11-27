-- Prove2me | solution 1 for GroundTheory.LocalField.unitsEquivIntProd_uniformizer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:47:44.524344+00:00
-- url     : https://prove2.me/submissions/f1a5f21e-a908-4088-9660-9c37c53f3fe7

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Theorems.Thm_GroundTheory_LocalField_unitsEquivIntProd_symm_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing
open scoped WithZero
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {K}
namespace GroundTheory.LocalField
theorem _root_.solution {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    unitsEquivIntProd hϖ (uniformizerUnit hϖ) = (Multiplicative.ofAdd 1, 1) := by
  rw [← MulEquiv.eq_symm_apply, unitsEquivIntProd_symm_apply]
  ext
  simp [coe_unitsOfIntProd]
end GroundTheory.LocalField
