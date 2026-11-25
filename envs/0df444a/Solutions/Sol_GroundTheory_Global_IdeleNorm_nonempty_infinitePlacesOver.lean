-- Prove2me | solution 1 for GroundTheory.Global.IdeleNorm.nonempty_infinitePlacesOver
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:06:54.287614+00:00
-- url     : https://prove2.me/submissions/1e2a4189-4002-4e9c-bafe-02fec9f89aa1

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalNorms
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_LocalFields_UnramifiedNorms
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalNormGroups

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField Filter Topology ValuativeRel
open AdeleBaseChange SemiLocal
open scoped NumberField.LiesOver TensorProduct
noncomputable section
open GroundTheory.Global.IdeleNorm
variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]
variable (L)
namespace GroundTheory.Global.IdeleNorm
theorem _root_.solution (v : InfinitePlace K) : Nonempty (v.placesOver L) := by
  obtain ⟨w, hw⟩ : ∃ w : InfinitePlace L, w.comap (algebraMap K L) = v :=
    InfinitePlace.comap_surjective v
  subst hw
  exact ⟨⟨w, (inferInstance : w.LiesOver (w.comap (algebraMap K L)))⟩⟩
end GroundTheory.Global.IdeleNorm
