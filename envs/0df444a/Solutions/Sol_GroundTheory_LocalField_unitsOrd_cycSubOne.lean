-- Prove2me | solution 1 for GroundTheory.LocalField.unitsOrd_cycSubOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:02:33.343464+00:00
-- url     : https://prove2.me/submissions/ac0099e2-a44b-4221-8cc2-61e270c96666

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_HerbrandCyclic
import Definitions.Def_GroundTheory_LocalFields_HilbertCyclic
import Definitions.Def_GroundTheory_LocalFields_UnitsGalois
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocalBase
import Theorems.Thm_GroundTheory_LocalField_unitsOrd_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel GroundTheory.GroupCoh GroundTheory.Global
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
namespace GroundTheory.LocalField
theorem _root_.solution (τ : L ≃ₐ[K] L) (x : Additive Lˣ) :
    unitsOrd L (cycSubOne (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) τ x) =
      cycSubOne (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ) τ (unitsOrd L x) := by
  rw [cycSubOne_apply, cycSubOne_apply, map_sub, Representation.ofMulDistribMulAction_apply_apply,
    unitsOrd_smul, Representation.trivial_apply]
  rfl
end GroundTheory.LocalField
