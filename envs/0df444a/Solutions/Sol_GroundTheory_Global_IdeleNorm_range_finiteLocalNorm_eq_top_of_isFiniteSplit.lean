-- Prove2me | solution 1 for GroundTheory.Global.IdeleNorm.range_finiteLocalNorm_eq_top_of_isFiniteSplit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:47:49.429797+00:00
-- url     : https://prove2.me/submissions/7445d829-2020-41dc-a6b8-e6108c7d2a83

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalNorms
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_LocalFields_UnramifiedNorms
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalNormGroups
import Theorems.Thm_GroundTheory_Global_IdeleNorm_finiteLocalNorm_mulSingle_algebraMap
import Theorems.Thm_GroundTheory_Global_nonempty_placesOver
import Theorems.Thm_GroundTheory_Global_splitsCompletely_iff_forall_finrank
import Theorems.Thm_GroundTheory_Global_splitsCompletely_iff_isFiniteSplit
import Theorems.Thm_GroundTheory_LocalField_IsUnramified_trans


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
namespace GroundTheory.Global.IdeleNorm
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K))
    (h : Algebra.IsFiniteSplit (v.adicCompletion K) (v.adicCompletion K ⊗[K] L)) :
    (finiteLocalNorm L v).range = ⊤ := by
  classical
  have hw := (splitsCompletely_iff_forall_finrank v).1 ((splitsCompletely_iff_isFiniteSplit v).2 h)
  obtain ⟨w⟩ := nonempty_placesOver L v
  refine eq_top_iff.2 fun a _ ↦ ⟨_, finiteLocalNorm_mulSingle_algebraMap v w a |>.trans ?_⟩
  rw [hw w, pow_one]
end GroundTheory.Global.IdeleNorm
