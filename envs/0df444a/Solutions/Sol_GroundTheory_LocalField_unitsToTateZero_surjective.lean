-- Prove2me | solution 1 for GroundTheory.LocalField.unitsToTateZero_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:50:38.949811+00:00
-- url     : https://prove2.me/submissions/778c8236-9fd6-40f6-9eeb-1e0dd5b33dca

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_HerbrandCyclic
import Definitions.Def_GroundTheory_LocalFields_HilbertCyclic
import Definitions.Def_GroundTheory_LocalFields_UnitsGalois
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocalBase

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
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
namespace GroundTheory.LocalField
theorem _root_.solution : Function.Surjective (unitsToTateZero (K := K) (L := L)) := by
  intro q
  obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk'_surjective _ q
  have hfix : ∀ y : L, (∀ g : L ≃ₐ[K] L, g y = y) → ∃ a : K, algebraMap K L a = y := fun y hy =>
    (IsGalois.mem_range_algebraMap_iff_fixed y).mpr hy
  obtain ⟨a, ha⟩ := hfix (x : L) fun g => congrArg Units.val (hx g)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact x.ne_zero ha.symm
  exact ⟨Units.mk0 a ha0, congrArg (QuotientGroup.mk' _) (Subtype.ext (Units.ext ha))⟩
end GroundTheory.LocalField
