-- Prove2me | solution 1 for GroundTheory.LocalField.intCast_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:07:25.920406+00:00
-- url     : https://prove2.me/submissions/4f240867-a825-4791-997a-de31d533bb29

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PadicExp
import Definitions.Def_GroundTheory_LocalFields_PrincipalUnitsModule
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
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p]
namespace GroundTheory.LocalField
theorem _root_.solution (c : ℤ) (u : Additive (unitFiltrationUnits K 1)) :
    ((c : ℤ_[p])) • u = c • u :=
  padicIntSMul_eq_of p fun k ↦ ⟨c, by simp, by simp⟩
end GroundTheory.LocalField
